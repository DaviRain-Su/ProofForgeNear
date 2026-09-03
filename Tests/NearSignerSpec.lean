import ProofForge
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Commands
import Examples.Near.NearSigner

open ProofForge
open Lean Elab Command

#pf_near_build Examples.Near.NearSigner

/-! A view entry reading a view-forbidden signer leaf; the emitter must fail closed. -/
namespace Tests.SignerViewBad

structure State where
  stamped : UInt64
  deriving Repr, DecidableEq, Inhabited

@[pf_entry]
def init : State :=
  { stamped := 0 }

@[pf_entry]
def get (_s : State) : UInt64 :=
  ProofForge.Wasm.Near.Runtime.signer


inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def noop (s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := (0 : UInt64) }, (0 : UInt64))
  else
    .error .overflow
end Tests.SignerViewBad

open Lean Elab Command in
elab "#pf_signer_view_reject " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .ok _ => throwError "expected near to reject {n.getId} (view reads signer)"
    | .error reason =>
      unless reason.contains "view cannot read signer" do
        throwError "unexpected rejection reason: {reason}"

#pf_signer_view_reject Tests.SignerViewBad

open Lean Elab Command in
elab "#pf_near_signer_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .error reason => throwError reason
    | .ok source =>
      unless source.contains "(import \"env\" \"signer_account_id\"" do
        throwError "NearSigner must import signer_account_id"
      unless source.contains "(import \"env\" \"signer_account_pk\"" do
        throwError "NearSigner must import signer_account_pk"

#pf_near_signer_emit_check Examples.Near.NearSigner
