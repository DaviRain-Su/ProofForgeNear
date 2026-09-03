# ProofForge NEAR

[![CI](https://github.com/DaviRain-Su/ProofForgeNear/actions/workflows/ci.yml/badge.svg)](https://github.com/DaviRain-Su/ProofForgeNear/actions/workflows/ci.yml)
[![Lean 4.31.0](https://img.shields.io/badge/Lean-v4.31.0-blue)](https://lean-lang.org)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

[中文](README.zh-CN.md)

**Write NEAR smart contracts in Lean 4, prove them with the Lean kernel, and
compile them to WebAssembly.** ProofForge NEAR is a Lean 4 → NEAR Wasm
compiler: mark contract entries with `@[pf_entry]` in ordinary Lean source,
and the extractor lowers them to a checked IR, emits WAT, and assembles
`.wasm` via **pinned wat2wasm** (wabt 1.0.41). The surface is **NEAR raw-u64**
with a near-sdk-style SDK, and every shipped fixture is gated on-chain by
**near-sandbox 2.13.0**. This repository is the NEAR single-target fork of
[ProofForge](https://github.com/DaviRain-Su/ProofForge).

## Features

- **Lean 4 as the contract language** — entries, state records, and errors are
  plain Lean `def`s / `structure`s / `inductive`s; theorems about them are
  proved in the same file (see `Examples/Counter.lean`).
- **Checked extraction pipeline** — `@[pf_entry]` → profile gate →
  target-neutral IR/CFG → NEAR dialect IR → WAT → `.wasm`. Registry-pinned
  digests fail the build if extraction output drifts.
- **near-sdk-style SDK** (`ProofForgeNearSdk`) — bounded storage
  (`Vector`/`Lookup`/`Iterable`/`Queue`), NEP-141 fungible-token ledger and
  registration economics, cross-contract **promises** (ordered N-way joins,
  callbacks), migrations with pinned prior-schema digests, and JSON boundary
  codecs (NEP-shaped args/results).
- **On-chain engineering gates** — near-sandbox deploys and calls every
  fixture: counter lifecycle, schema migration, promise joins, storage,
  NEP-141 events.
- **Pinned toolchain** — Lean/Lake v4.31.0, wabt wat2wasm 1.0.41,
  near-sandbox 2.13.0 (`.agents/setup`).

## Example

```lean
import ProofForge

namespace MyCounter

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (initial : UInt64) : State :=
  { value := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

/-- Checked add: on overflow the entry fails and state stays put. -/
@[pf_entry]
def increment (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if s.value ≤ u64Max - delta then
    let next := s.value + delta
    .ok ({ value := next }, next)
  else
    .error .overflow

end MyCounter
```

```text
lake exe pf -- build --module MyCounter.Counter   # writes Counter.wat / Counter.wasm
```

## Build & test

```text
./.agents/setup        # pinned toolchain: elan/Lake v4.31.0, wat2wasm 1.0.41, near-sandbox 2.13.0
lake build             # compiler library
lake build pf          # CLI executable
lake build Tests       # test suite (elaboration-time assertions)
lake build Examples    # example contracts
```

Local CI mirror: `scripts/ci_local.sh` (`--fast` runs the Python guards only).

## CLI

```text
pf build [--out DIR] [--module MOD] [Program ...]
pf --version
```

`pf build` writes `Name.wat` / `Name.wasm` (NEAR raw-u64; locked wat2wasm).
Bare names map to in-tree `Examples` fixtures; user projects pass `--module`
or list `[[program]]` entries in `pf.toml`.

## On-chain gates

```text
runtime-tests/near/check.sh      # NEAR import-table + wasm magic
runtime-tests/near/counter.sh    # near-sandbox Counter (skips when sandbox is absent)
```

## Layout

- `ProofForge/Core/` — target-independent value/effect IR, CFG, codec, schema
- `ProofForge/Extract/` — Lean expression → IR extractor (NEAR-only)
- `ProofForge/Wasm/` — family Host / IR / Emit plus `Near/`
- `ProofForge/Cli.lean` — the `pf` CLI (`pf build`)
- `Examples/` — NEAR fixtures (digests pinned in `ProofForge/Wasm/Near/Registry.lean`)
- `Tests/` — elaboration-time specs (`#guard` / `example`)
- `runtime-tests/near/` — near-sandbox 2.13.0 integration gates
- `docs/product/` — support matrix, writing guide, roadmap
- `docs/research/` — **historical** decision notes (archived)
- `docs/modules/` — per-module contracts

## User contracts

Contracts import only `ProofForge.Attr` plus the NEAR SDK — never the
`ProofForge` umbrella:

```lean
import ProofForge.Attr
import ProofForge.Wasm.Near.Sdk
```

The SDK transitive closure must not reach Emit/Assemble/Registry (enforced in CI
by `scripts/check_sdk_import_closure.py`). Lake lib: `ProofForgeNearSdk`.

## Trust boundary

- Kernel theorems are about user `def`s / static fields — **not** about `.wasm` refinement.
- near-sandbox green is an **engineering** gate, not a proof.
- NEAR JSON / NEP-shaped exports are **bounded canonical subsets**, not full standard ABIs.

## Related repositories

- [ProofForge](https://github.com/DaviRain-Su/ProofForge) — multi-target upstream monorepo
- [ProofForgeEvm](https://github.com/DaviRain-Su/ProofForgeEvm) — EVM single-target fork
- [ProofForgeXrpl](https://github.com/DaviRain-Su/ProofForgeXrpl) — XRPL single-target fork

## License

[MIT](LICENSE) © 2026 DaviRain-Su
