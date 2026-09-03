import Examples.Near.NearJsonI64Input
import Lean
import ProofForge

/-! Canonical unquoted JSON integer (i64) input invariants. -/

namespace Tests.NearJsonI64InputSpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Codec.maxJsonI64Whitespace == 32
#guard Codec.maxJsonI64InputBytes == 156
#guard match Codec.targetInputPlan Codec.nearI64Schema with
  | .ok .jsonI64 => true
  | _ => false
#guard match Codec.targetInputPlan (.scalar .uint64) with
  | .error _ => true
  | _ => false

elab "#pf_near_json_i64_input_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Near.NearJsonI64Input with
    | .ok program => pure program
    | .error reason => throwError reason
  let some sourceEcho := source.methods.find? (·.ixName == "echoValue")
    | throwError "missing source echoValue"
  let some sourceCommit := source.methods.find? (·.ixName == "commitValue")
    | throwError "missing source commitValue"
  unless sourceEcho.paramSchemas.size == 1 && sourceCommit.paramSchemas.size == 1 do
    throwError "extractor lost the NearI64 input parameter"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let policy :=
    "near-json-i64-number-canonical-v1(max-wire=156,ws=32,range=[-2^63,2^63-1],unknown=reject)"
  for method in program.entries do
    if method.ixName == "echoValue" || method.ixName == "commitValue" then
      unless method.inputSchema == some Codec.nearI64Schema && method.inputPolicy == policy &&
          method.paramCount == 1 do
        throwError s!"target lost the JSON i64 input plan for {method.ixName}"
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(func $pf_json_i64_amount",
    "(i64.const 156)",
    "(call $pf_arena_alloc (i64.const 8) (i64.const 8))",
    "(call $pf_input (i64.const 0))",
    "(call $pf_read_register (i64.const 0) (i64.extend_i32_u (local.get $pf_input_ptr)))",
    "(call $pf_json_i64_amount (local.get $pf_input_ptr)",
    "(i64.load (local.get $pf_i64_ptr))"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR JSON i64 WAT missing {anchor}"
  unless (wat.splitOn "(func $pf_json_i64_amount").length == 2 do
    throwError "JSON i64 parser helper must be emitted exactly once"
  for exportName in #["echoValue", "commitValue"] do
    let parts := wat.splitOn s!"(func (export \"{exportName}\")"
    unless parts.length == 2 do throwError s!"missing unique {exportName} export"
  logInfo m!"proofforge-near-json-i64-input: digest = {IR.digestHex program}"

#pf_near_json_i64_input_check

end Tests.NearJsonI64InputSpec