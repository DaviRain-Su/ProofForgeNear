import Lake
open Lake DSL

package «proofforge» where
  version := v!"0.0.1"

/-- Shared Attr + Core/Crypto surface used by the NEAR SDK. -/
lean_lib ProofForgeCore where
  roots := #[
    `ProofForge.Attr,
    `ProofForge.Core.Codec,
    `ProofForge.Core.Collections,
    `ProofForge.Core.Math,
    `ProofForge.Core.Ops,
    `ProofForge.Core.SafeCast,
    `ProofForge.Core.Value
  ]

/-- Contract-facing NEAR SDK (+ Runtime needed for `pf_inline` erase). No Emit. -/
lean_lib ProofForgeNearSdk where
  roots := #[
    `ProofForge.Wasm.Near.Codec,
    `ProofForge.Wasm.Near.Memory,
    `ProofForge.Wasm.Near.Runtime,
    `ProofForge.Wasm.Near.Sdk,
    `ProofForge.Wasm.Near.Sdk.Fungible.Ledger,
    `ProofForge.Wasm.Near.Sdk.Fungible.Registration,
    `ProofForge.Wasm.Near.Sdk.Promise,
    `ProofForge.Wasm.Near.Sdk.Storage,
    `ProofForge.Wasm.Near.Sdk.Store.AccountTokenLookup,
    `ProofForge.Wasm.Near.Sdk.Store.Codec,
    `ProofForge.Wasm.Near.Sdk.Store.Iterable,
    `ProofForge.Wasm.Near.Sdk.Store.Lookup,
    `ProofForge.Wasm.Near.Sdk.Store.Queue,
    `ProofForge.Wasm.Near.Sdk.Store.Vector,
    `ProofForge.Wasm.Near.Sdk.Transient
  ]

/-- Compiler: Extract, Wasm NEAR IR/Emit/Assemble/Registry, and the `ProofForge` umbrella.
This `lean_lib` is the in-repo compiler workspace.
User templates must depend on `ProofForgeNearSdk` / `ProofForgeCore` only. -/
@[default_target]
lean_lib ProofForge where
  roots := #[
    `ProofForge,
    `ProofForge.Cli,
    `ProofForge.Core.CFG,
    `ProofForge.Core.Eval,
    `ProofForge.Core.FixedPoint,
    `ProofForge.Core.IR,
    `ProofForge.Core.Schema,
    `ProofForge.Core.Target,
    `ProofForge.Crypto.Keccak,
    `ProofForge.Crypto.Sha256,
    `ProofForge.Crypto.Sha256Compat,
    `ProofForge.Extract,
    `ProofForge.Extract.Decode,
    `ProofForge.Extract.IR,
    `ProofForge.Extract.Lexical,
    `ProofForge.Extract.Ops,
    `ProofForge.Profile,
    `ProofForge.Wasm.Emit,
    `ProofForge.Wasm.Host,
    `ProofForge.Wasm.IR,
    `ProofForge.Wasm.Near.Assemble,
    `ProofForge.Wasm.Near.Commands,
    `ProofForge.Wasm.Near.Emit,
    `ProofForge.Wasm.Near.Host,
    `ProofForge.Wasm.Near.IR,
    `ProofForge.Wasm.Near.Ops,
    `ProofForge.Wasm.Near.Registry
  ]

/-- Build every module under `Examples/` (NEAR fixtures only). -/
lean_lib Examples where
  globs := #[.one `Examples, .submodules `Examples]

lean_lib Tests

lean_exe pf where
  root := `ProofForge.Cli
  supportInterpreter := true
