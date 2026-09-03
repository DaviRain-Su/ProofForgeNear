import ProofForge
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Commands
import Examples.Near.NearChain

open ProofForge
open Lean Elab Command

#pf_near_build Examples.Near.NearChain

open Lean Elab Command in
elab "#pf_near_chain_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .error reason => throwError reason
    | .ok source =>
      unless source.contains "(import \"env\" \"epoch_height\"" do
        throwError "NearChain must import epoch_height"
      unless source.contains "(import \"env\" \"account_locked_balance\"" do
        throwError "NearChain must import account_locked_balance"
      unless source.contains "(import \"env\" \"random_seed\"" do
        throwError "NearChain must import random_seed"
      unless source.contains "(import \"env\" \"prepaid_gas\"" do
        throwError "NearChain must import prepaid_gas"
      unless source.contains "(import \"env\" \"used_gas\"" do
        throwError "NearChain must import used_gas"

#pf_near_chain_emit_check Examples.Near.NearChain
