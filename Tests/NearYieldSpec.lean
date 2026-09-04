import Examples.Near.NearYield
import Lean
import ProofForge

/-! Resumable yield promise pipeline invariants. -/

namespace Tests.NearYieldSpec

open Lean Elab Command
open ProofForge.Wasm.Near

elab "#pf_near_yield_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Near.NearYield with
    | .ok program => pure program
    | .error reason => throwError reason
  let some scheduleSource := source.methods.find? (·.ixName == "scheduleYield")
    | throwError "missing source scheduleYield"
  let some resumeSource := source.methods.find? (·.ixName == "resumeYield")
    | throwError "missing source resumeYield"
  unless scheduleSource.paramCount == 1 && resumeSource.paramCount == 1 do
    throwError "extractor lost the yield entry parameters"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(import \"env\" \"promise_yield_create\"",
    "(import \"env\" \"promise_yield_resume\"",
    "(func (export \"scheduleYield\")",
    "(func (export \"resumeYield\")",
    "(call $pf_promise_yield_create",
    "(call $pf_promise_yield_resume"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR yield WAT missing {anchor}"
  logInfo m!"proofforge-near-yield: digest = {IR.digestHex program}"

#pf_near_yield_check

end Tests.NearYieldSpec