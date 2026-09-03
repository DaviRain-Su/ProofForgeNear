# Modules

| Module | Contract |
|---|---|
| [Crypto](crypto.md) | Native SHA-256 / Keccak-256 |
| [Attr](attr.md) | `@[pf_entry]` marker |
| [IR](ir.md) | `Core.IR` program shape + `Core.Target` registration + NEAR physical layout |
| [Profile](profile.md) | Transitive-closure profile |
| [Ops](ops.md) | Expr operation sequence |
| [Extract](extract.md) | Expr → IR + ops; any user project |
| [Emit](emit.md) | `Wasm.Emit` / `Near.Emit`: Core → WAT |
| [Assemble](assemble.md) | locked `wat2wasm` → `.wasm` |
| [Cli](cli.md) | `pf build` |
| [Runtime](runtime.md) | `Wasm.Near.Runtime` host stubs |
| [Wasm](wasm.md) | NEAR wasm lowering: Lean → `.wasm`; `env` host imports and KV layout |
| [Near](near.md) | `Wasm/Near`: NEAR Protocol; `env` + KV raw-u64 |
