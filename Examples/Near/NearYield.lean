import ProofForge

namespace Examples.Near.NearYield
open ProofForge.Core.Value
open ProofForge.Wasm.Near.Runtime
open ProofForge.Wasm.Near.Sdk

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] private def callGas : UInt64 := 20_000_000_000_000

@[pf_entry]
def init (seed : UInt64) : State :=
  { marker := seed }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

/-- Schedule a resumable yield self-call to `get` with empty arguments. The promise index is
dropped by the detached surface; the sandbox gate drives the resume from outside. -/
@[pf_entry]
def scheduleYield (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let dataId : ProofForge.Wasm.Near.Runtime.CryptoBytes32 :=
    { w0 := 0, w1 := 0, w2 := 0, w3 := 0 }
  let _ := Promises.yieldCreate "get"
    (ProofForge.Wasm.Near.Sdk.Store.borshUInt64 value) dataId callGas 1
  .ok ({ state with marker := value }, value)

/-- Resume a pending yield with the exact data id and empty payload, returning the raw host
status (1 if the yield was resumed, 0 otherwise). -/
@[pf_entry]
def resumeYield (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let dataId : BoundedBytes 32 := { length := 32, values := #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }
  let payload : BoundedBytes 1 := { length := 0, values := #v[0] }
  let status := Promises.yieldResume dataId payload
  .ok ({ state with marker := status }, status)

end Examples.Near.NearYield