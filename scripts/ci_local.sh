#!/usr/bin/env bash
# Local CI mirror for ProofForge NEAR — run the same lane gates *before* pushing.
#
# Usage:
#   scripts/ci_local.sh                  # auto lanes from git diff vs origin/main
#   scripts/ci_local.sh --fast           # python guards only
#   scripts/ci_local.sh --lane lean
#   scripts/ci_local.sh --lane near
#   scripts/ci_local.sh --all            # every lane
#   scripts/ci_local.sh --base origin/main
#
# Env: CI_LOCAL_BASE, SKIP_SETUP=1
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

BASE="${CI_LOCAL_BASE:-origin/main}"
FAST=0
ALL=0
declare -a LANES=()

usage() { sed -n '2,14p' "$0" | sed 's/^# \{0,1\}//'; exit "${1:-0}"; }

while [[ $# -gt 0 ]]; do
  case "$1" in
    --fast) FAST=1 ;;
    --all) ALL=1 ;;
    --lane) shift; LANES+=("$1") ;;
    --base) shift; BASE="$1" ;;
    -h|--help) usage 0 ;;
    *) echo "unknown arg: $1" >&2; usage 1 ;;
  esac
  shift
done

log() { printf '\n==> %s\n' "$*"; }

have_lane() {
  local want="$1" l
  for l in "${LANES[@]:-}"; do [[ "$l" == "$want" ]] && return 0; done
  return 1
}

matches_any() {
  local f="$1" pat
  shift
  for pat in "$@"; do
    case "$f" in $pat) return 0 ;; esac
  done
  return 1
}

detect_lanes() {
  git rev-parse --verify "$BASE" >/dev/null 2>&1 || git fetch origin main 2>/dev/null || true
  local mb
  mb="$(git merge-base HEAD "$BASE" 2>/dev/null || git rev-parse HEAD)"
  mapfile -t CHANGED < <({
    git diff --name-only "$mb" HEAD
    git diff --name-only --cached
    git diff --name-only
  } | awk 'NF && !seen[$0]++')

  if ((${#CHANGED[@]} == 0)); then
    log "no changed files vs $BASE — defaulting to lean+near"
    LANES=(lean near)
    return
  fi
  printf 'changed files (merge-base %s):\n' "$mb" >&2
  printf '  %s\n' "${CHANGED[@]}" >&2

  local lean=0 near=0 shared=0 f
  for f in "${CHANGED[@]}"; do
    matches_any "$f" \
      '.github/workflows/ci.yml' '.agents/setup' 'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' \
      'ProofForge/Cli.lean' 'ProofForge/Attr.lean' 'ProofForge/Extract.lean' 'ProofForge/Extract/**' \
      'ProofForge/Core/**' 'ProofForge/Crypto/**' 'ProofForge/Profile.lean' && shared=1
    matches_any "$f" \
      'ProofForge/**' 'Tests/**' 'Tests.lean' 'Examples/**' 'Examples.lean' \
      'scripts/check_*.py' 'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' \
      '.github/workflows/ci.yml' '.agents/setup' && lean=1
    matches_any "$f" \
      'ProofForge/Wasm/**' 'Examples/Near/**' 'Examples/*.lean' 'Examples.lean' \
      'runtime-tests/near/**' 'scripts/check_artifact_manifest.py' \
      'lakefile.lean' 'lean-toolchain' 'lake-manifest.json' '.github/workflows/ci.yml' '.agents/setup' \
      'ProofForge/Cli.lean' 'ProofForge/Extract.lean' 'ProofForge/Extract/**' 'ProofForge/Core/**' && near=1
  done
  if (( shared )); then lean=1; near=1; fi
  LANES=()
  (( lean )) && LANES+=(lean)
  (( near )) && LANES+=(near)
  if ((${#LANES[@]} == 0)); then
    log "docs only — running --fast guards"
    FAST=1
    LANES=(guards)
  fi
}

if (( FAST )); then
  LANES=(guards)
elif (( ALL )); then
  LANES=(lean near)
elif ((${#LANES[@]} == 0)); then
  detect_lanes
fi

log "lanes: ${LANES[*]-none}  fast=${FAST}"

if [[ "${SKIP_SETUP:-0}" != "1" && "$FAST" != "1" ]]; then
  if [[ -x .agents/setup ]]; then
    log "Prepare pinned toolchains (.agents/setup)"
    ./.agents/setup
    export PATH="$HOME/.local/bin:$HOME/.elan/bin:${PATH:-}"
  fi
fi

run_guards() {
  log "Python ownership / SDK / manifest / no-sorry guards"
  python3 scripts/check_ownership.py
  python3 scripts/check_sdk_import_closure.py
  python3 scripts/check_artifact_manifest.py --self-test
  python3 scripts/check_no_sorry.py
}

run_lean() {
  run_guards
  log "lake build + formalization gates + Tests"
  lake build
  lake build ProofForgeNearSdk
  lake build Tests.ProofSpec
  lake build Tests
}

run_near() {
  log "NEAR lane"
  lake build Examples
  lake exe pf -- build --out build/near
  python3 scripts/check_artifact_manifest.py --target near --out build/near
  local s
  for s in \
    check counter context chain signer crypto lazy bytes ft_event token_arithmetic token_storage memory output \
    storage_balance_output storage_balance_bounds_output \
    json_account_input json_amount_input json_memo_input json_message_input \
    json_ft_transfer_input json_ft_transfer_call_input json_ft_on_transfer_input \
    ft_receiver_value promise_or_value json_ft_resolve_input \
    json_storage_deposit_input json_storage_unregister_input json_storage_withdraw_input \
    json_boolean_mutation storage storage_economics storage_registration \
    vector lookup ledger queue iterable promise
  do
    log "NEAR ${s}"
    "runtime-tests/near/${s}.sh"
  done
}

if (( FAST )) || have_lane guards; then
  run_guards
fi
have_lane lean && run_lean
have_lane near && run_near

log "ci_local: OK (lanes: ${LANES[*]-none})"
