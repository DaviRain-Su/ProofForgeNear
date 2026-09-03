import Examples.Near.NearLazy
import Lean
import ProofForge

/-! Bounded direct NEAR Lazy/LazyOption cell layout, extraction, and WAT invariants. -/

namespace Tests.NearLazySpec

open Lean Elab Command
open ProofForge.Wasm.Near
open ProofForge.Wasm.Near.Sdk.Store

#guard LazyCell.wellFormed 0xffffffff
#guard !LazyCell.wellFormed 0x100000000
#guard LazyOptionCell.wellFormed 0x31545054

private def key : ProofForge.Core.Value.BoundedBytes 4 :=
  (0x315a414c : LazyCell).elementKey

#guard key.length == 4
#guard key.values[0] == 0x4c
#guard key.values[1] == 0x41
#guard key.values[2] == 0x5a
#guard key.values[3] == 0x31

private def value : ProofForge.Core.Value.BoundedBytes 8 :=
  LazyCell.elementValue 0x0102030405060708

#guard value.length == 8
#guard value.values[0] == 0x08
#guard value.values[7] == 0x01

private partial def storageSteps : Array ProofForge.Extract.IR.Op → Array String
  | ops => ops.foldl (init := #[]) fun steps op =>
      steps ++ match op with
      | .ext (.near (.storageRead result key _)) => #[s!"read.{result}.{key}"]
      | .ext (.near (.storageWrite result key _ _ _)) => #[s!"write.{result}.{key}"]
      | .ext (.near (.storageHasKey result key _)) => #[s!"has.{result}.{key}"]
      | .ext (.near (.storageRemove result key _)) => #[s!"remove.{result}.{key}"]
      | .ite _ _ _ thn els => storageSteps thn ++ storageSteps els
      | .forBody _ body => storageSteps body
      | _ => #[]

elab "#pf_near_lazy_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Near.NearLazy with
    | .ok program => pure program
    | .error reason => throwError reason
  let steps (name : String) :=
    (source.methods.find? (·.ixName == name)).map (storageSteps ·.ops) |>.getD #[]
  unless steps "lazyGet" == #["read.8.4"] &&
      steps "lazySet" == #["write.8.4"] &&
      steps "optIsSome" == #["has.8.4"] &&
      steps "optSet" == #["write.8.4"] &&
      steps "optTake" == #["read.8.4", "remove.8.4"] do
    throwError s!"Lazy cell storage effects were lost or reordered: " ++
      s!"lazyGet={steps "lazyGet"}, lazySet={steps "lazySet"}, " ++
      s!"optIsSome={steps "optIsSome"}, optSet={steps "optSet"}, optTake={steps "optTake"}"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let wat ←
    match Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(func (export \"lazyGet\")",
    "(func (export \"lazySet\")",
    "(func (export \"lazyGetOrSet\")",
    "(func (export \"optIsSome\")",
    "(func (export \"optGet\")",
    "(func (export \"optSet\")",
    "(func (export \"optTake\")",
    "(call $pf_storage_write",
    "(call $pf_storage_read",
    "(call $pf_storage_remove",
    "(call $pf_storage_has_key",
    "(i64.const 827998540)",
    "(i64.const 827609172)"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR LazyCell WAT missing {anchor}\n{wat}"
  logInfo m!"proofforge-near-lazy: digest = {IR.digestHex program}"

#pf_near_lazy_check

end Tests.NearLazySpec