import ProofForge

namespace Examples.Near.NearJsonI64Input
open ProofForge.Core.Value

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (marker : UInt64) : State :=
  { marker }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

/-! These methods exercise the compiler-owned canonical unquoted JSON integer input.
They are codec fixtures, not public ABI methods or a generic JSON wrapper. -/

@[pf_entry]
def echoValue (_state : State) (input : ProofForge.Wasm.Near.Runtime.NearI64) : UInt64 :=
  input.value

@[pf_entry]
def commitValue (_state : State) (input : ProofForge.Wasm.Near.Runtime.NearI64) :
    Except Error (State × UInt64) :=
  .ok ({ marker := input.value }, input.value)

end Examples.Near.NearJsonI64Input