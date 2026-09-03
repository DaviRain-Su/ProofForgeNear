import ProofForge
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Commands
import Examples.Near.NearCrypto

open ProofForge
open Lean Elab Command

#pf_near_build Examples.Near.NearCrypto

open Lean Elab Command in
elab "#pf_near_crypto_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .error reason => throwError reason
    | .ok source =>
      unless source.contains "(import \"env\" \"sha256\"" do
        throwError "NearCrypto must import sha256"
      unless source.contains "(import \"env\" \"keccak256\"" do
        throwError "NearCrypto must import keccak256"
      unless source.contains "(import \"env\" \"keccak512\"" do
        throwError "NearCrypto must import keccak512"
      unless source.contains "(import \"env\" \"ripemd160\"" do
        throwError "NearCrypto must import ripemd160"
      unless source.contains "(import \"env\" \"ecrecover\"" do
        throwError "NearCrypto must import ecrecover"
      unless source.contains "(import \"env\" \"ed25519_verify\"" do
        throwError "NearCrypto must import ed25519_verify"

#pf_near_crypto_emit_check Examples.Near.NearCrypto
