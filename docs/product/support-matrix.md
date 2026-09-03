# Support matrix (v0 product surface)

> Status: living product contract. If README and this file disagree, **this file wins**.

## Product one-liner

ProofForge NEAR is a **checkout-first Lean 4 → WAT → wat2wasm** compiler for a fail-closed NEAR raw-u64 subset, with near-sandbox engineering gates. It is **not** a mainnet deployment product, not a full NEP suite, and not a proved-bytecode toolchain.

## Target

| Target | Product status | CI posture | Notes |
|---|---|---|---|
| NEAR (implicit) | **Supported** | Required merge gate | Emits `.wat` / `.wasm`; locked wat2wasm 1.0.41; near-sandbox 2.13.0 |
| bare `wasm` | **Rejected** | — | Family name, not a chain; this build of `pf` supports NEAR only |

## CLI surface

| Command | Status |
|---|---|
| `pf build` | Supported |
| `pf --version` / `-h` | Supported |
| `pf deploy` / `pf call` / `pf init` / `doctor` / `install` | **Not implemented** |

## Language / extract subset

| Area | Status |
|---|---|
| Ordinary `def` / `structure` / `Except` entries with `@[pf_entry]` | Supported |
| Profile refuse IO / partial / sorry / extern / unbounded recursion | Supported |
| Checked arithmetic, `ite`, `storeField`, named errors | Supported |
| NEAR `env` imports, bounded Borsh/JSON ABI, collections, Promise | Supported (bounded, fail-closed) |
| Foreign-chain leaves at extract time | **Refused** (fail-closed) |
| Dynamic callee / unbounded loops / generic JSON codecs | **Out of scope** |

## SDK naming honesty

| Module | Say this | Do **not** say this |
|---|---|---|
| `Wasm.Near.Sdk` | Bounded NEAR raw-u64 / Borsh / NEP-shaped subset | Complete NEP-141/145/148 ABI |
| `deployable=false` on `pf build` | Engineering artifacts | Public-network endorsement |
| `Near.Sdk.Hash` | View-safe `sha256` / `keccak256` / `keccak512` / `ripemd160` / `ecrecover` / `ed25519_verify` with known-vector sandbox gates | Ethereum-style 27/28 `v`, keccak = SHA3, variable-length signatures |
| `Near.Sdk.Store.Lazy` / `LazyOption` | Bare-prefix single-value `UInt64` cells with immediate writes | Rust cache/`Drop` flush timing, generic value types |
| `Near.Sdk.Context` (signer/gas/chain) | `signer_account_id`/`pk`, `epoch_height`, `prepaid_gas`/`used_gas`, `account_locked_balance`, `random_seed`, `state_exists` | Full near-sdk `env` surface |

## Proof boundary

| Claim | Status |
|---|---|
| Kernel-checked theorems about user `def` / static fields | Yes (examples + no-sorry CI) |
| Theorems about host storage / world state | Not yet |
| Theorems about WAT / `.wasm` refinement | **Not claimed** |
| near-sandbox green ⇒ proved on-chain behavior | **Not claimed** (engineering gate only) |

## User-project path (supported)

From repo root after toolchain setup:

```bash
lake build pf
lake exe pf -- build --out build/near
```

A standalone installer / release tarball is roadmap work, not v0.

## Related

- Writing guide: [writing-contracts.md](writing-contracts.md)
- Roadmap: [roadmap.md](roadmap.md)
- Module internals: [../modules/](../modules/)
- Historical research (archived): [../research/](../research/)
