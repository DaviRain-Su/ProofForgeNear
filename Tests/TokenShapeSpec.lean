import ProofForge
import ProofForge.Wasm.Near.Commands
import Examples.TokenShape

/-!
# TokenShape conformance (NEAR)

`Examples.TokenShape` is the **transfer-shaped** UInt64 ledger subset (`initialize` / `get` /
`credit` / `debit`). The NEAR digest is pinned below and in `ProofForge.Wasm.Near.Registry`.
-/

namespace Tests.TokenShapeSpec

#guard ProofForge.Wasm.Near.Registry.digestOf "TokenShape" == some "f824063d978669c6"

open Lean Elab Command
open ProofForge
elab "#pf_token_shape_check" : command => do
  let env ← getEnv
  let module := `Examples.TokenShape
  let nearProgram ←
    match Extract.extractModuleIR env module none >>= ProofForge.Wasm.Near.IR.fromExtracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let nearDigest := ProofForge.Wasm.Near.IR.digestHex nearProgram
  unless nearDigest == "f824063d978669c6" do
    throwError s!"TokenShape digest mismatch: near={nearDigest}"
  let shared := #["credit", "debit", "get", "initialize"]
  let nearMethods :=
    (#[nearProgram.initializer.ixName] ++ nearProgram.entries.map (·.ixName)) |>.qsort (· < ·)
  unless nearMethods == shared do
    throwError s!"TokenShape method surface diverged: near={nearMethods}"
  logInfo m!"token-shape: near={nearDigest}"

#pf_token_shape_check

#pf_near_build Examples.TokenShape

end Tests.TokenShapeSpec
