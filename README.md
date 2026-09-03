# ProofForge NEAR

[![CI](https://github.com/DaviRain-Su/ProofForgeNear/actions/workflows/ci.yml/badge.svg)](https://github.com/DaviRain-Su/ProofForgeNear/actions/workflows/ci.yml)

[中文](README.zh-CN.md)

A Lean 4 → NEAR contract compiler. Mark entries with `@[pf_entry]` in ordinary
Lean source; ProofForge extracts a checked IR, emits WAT, and assembles `.wasm`
via **pinned wat2wasm** (wabt 1.0.41). The surface is **NEAR raw-u64** with a
near-sdk-style SDK and **near-sandbox** engineering gates. This repository is
the NEAR single-target fork of ProofForge.

Product contract: [`docs/product/support-matrix.md`](docs/product/support-matrix.md).
Writing guide: [`docs/product/writing-contracts.md`](docs/product/writing-contracts.md).

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
