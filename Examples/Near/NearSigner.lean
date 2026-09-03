import ProofForge

/-!
Signer fixture: `signer_account_id` and `signer_account_pk` are the transaction
signer's identity (view-forbidden). `signer != predecessor` whenever the call
arrives through a promise chain, so these entries pin the distinction.
-/
namespace Examples.Near.NearSigner
open ProofForge.Wasm.Near.Sdk

structure State where
  stamped : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init : State :=
  { stamped := 0 }

/-- 入口：签名者账户 id 前 8 字节 LE。view 禁止。 -/
@[pf_entry]
def signerId (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.signerLo }, Context.signerLo)
  else
    .error .overflow

/-- 入口：签名者账户 id 的实际 UTF-8 字节数。 -/
@[pf_entry]
def signerIdLength (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.signer.length }, Context.signer.length)
  else
    .error .overflow

/-- 入口：签名者公钥第一窗口(曲线标签字节 + 密钥字节 0..7,小端)。 -/
@[pf_entry]
def signerKeyLo (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.signerPkW0 }, Context.signerPkW0)
  else
    .error .overflow

/-- 入口：签名者公钥最后窗口(仅密钥字节 32)。 -/
@[pf_entry]
def signerKeyTop (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.signerPkW4 }, Context.signerPkW4)
  else
    .error .overflow

/-- 入口鉴权:签名者与直接调用者完整相等(非 promise 链回调)。 -/
@[pf_entry]
def checkDirectCall (_s : State) : Except Error (State × UInt64) :=
  if AccountId.eq Context.signer Context.caller then
    .ok ({ stamped := 1 }, 1)
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.stamped

end Examples.Near.NearSigner
