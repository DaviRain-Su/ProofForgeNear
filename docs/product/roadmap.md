# Product roadmap

## Already landed

- NEAR-only module docs under `docs/modules/`
- NEAR raw-u64 as the CI lane
- Compiler/SDK slice coverage well past the old W0–W3 research cut (`docs/research/06-wasm-feasibility.md`)

## Now (product surface)

1. **Honest public claims** — README matches CLI + CI reality (wat2wasm supported, no fake installer).
2. **Support matrix + writing guide** — this directory.
3. **Checkout quickstart that is copy-paste true** — `lake build pf` → `pf build`.
4. **Research archive banners** — `docs/research/06-wasm-feasibility.md` marked historical.

## Next

5. **Release v0.1** — tagged `pf` binary + Lake `require … @ tag` path.
6. **Init template** — a checkout-local `pf init` for a NEAR counter (not claimed today).

## Later (compiler depth; not P0 product copy)

7. Effect representation cleanup where dummy/hold still leaks into examples.
8. Broader NEAR JSON without pretending full NEP compatibility.

## Explicit non-goals

Dynamic callee, unbounded recursion, mainnet endorsement, bytecode refinement proofs, a generic “wasm” target name.
