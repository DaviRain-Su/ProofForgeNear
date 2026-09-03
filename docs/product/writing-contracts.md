# Writing contracts (v0)

## Imports

User projects should import only the attribute marker and the NEAR SDK:

```lean
import ProofForge.Attr
import ProofForge.Wasm.Near.Sdk
```

Do **not** import the `ProofForge` umbrella (it can pull Emit / Assemble / Registry).

## Entry shape

Mark chain entries with `@[pf_entry]`. Keep state in an explicit `structure`, errors in an `inductive`, and mutations as `Except`-style transitions when you need revert.

In-tree starting points: `Examples/Counter.lean` (shared scalar), `Examples/Near/NearCtx.lean`.

## What works today

- Checked `UInt64` math and fail-closed Profile
- NEAR: `env` context, bounded Borsh/JSON frames, raw storage, direct collections, detached/returned Promise
- Kernel proofs about the Lean `def` (not about `.wasm`)

## Known sharp edges (be honest in examples)

1. **Bounded ABI** — NEAR JSON/Borsh parsers reject unknown keys, escaped keys, and over-capacity strings. They are not serde.
2. **`deployable=false` on `pf build`** — assembly is not a public-deployment claim.

These are product debts tracked in [roadmap.md](roadmap.md), not undocumented folklore.

## Build

```bash
lake build
lake exe pf -- build --out build/near
```

Artifacts: `Name.wat`, `Name.wasm`.

## Prove

Keep theorems next to the contract. CI refuses `sorry` in the proof batch. Prove properties of the Lean function; do not claim the theorem proved the `.wasm`.
