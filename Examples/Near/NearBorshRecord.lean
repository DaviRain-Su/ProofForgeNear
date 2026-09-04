import ProofForge

namespace Examples.Near.NearBorshRecord
open ProofForge.Core.Value

structure State where
  left : UInt64
  right : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Two-leaf summary record serialized by the Borsh record output serializer:
declaration-order UInt64 fields as raw little-endian concatenation (no tag, no prefix). -/
structure Summary where
  total : UInt64
  version : UInt64
  deriving Repr, DecidableEq, Inhabited

@[pf_entry] def init : State := { left := 0, right := 0 }
@[pf_entry] def get (state : State) : UInt64 := state.left
@[pf_entry] def spare (state : State) : UInt64 := state.right

@[pf_entry]
def commit (_state : State) (next : UInt64) : Except Error (State × Summary) :=
  if next != 0 then
    .ok ({ left := next, right := 0x8877665544332211 }, { total := next, version := 7 })
  else
    .error .overflow

end Examples.Near.NearBorshRecord
