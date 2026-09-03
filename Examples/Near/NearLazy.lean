import ProofForge

namespace Examples.Near.NearLazy
open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk.Storage
open ProofForge.Wasm.Near.Sdk.Store

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- N15: bare prefix `LAZ1` (`0x315a414c`). -/
@[pf_inline] def cell : LazyCell.Handle :=
  LazyCell.handle 0x315a414c

/-- bare prefix `OPT1` (`0x31545054`). -/
@[pf_inline] def optCell : LazyOptionCell.Handle :=
  LazyOptionCell.handle 0x31545054

@[pf_entry]
def init (marker : UInt64) : State :=
  { marker }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

@[pf_entry]
def lazyGet (_state : State) : UInt64 :=
  cell.getD 0

@[pf_entry]
def lazySet (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let status := cell.set value
  .ok ({ marker := status }, status)

@[pf_entry]
def lazyGetOrSet (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let buffer : ResultBuffer := 8
  let _ := buffer.read (LazyCell.elementKey cell.tag)
  if buffer.status == 1 then
    let present :=
      (buffer.byte 0).toUInt64 |||
        ((buffer.byte 1).toUInt64 <<< 8) |||
        ((buffer.byte 2).toUInt64 <<< 16) |||
        ((buffer.byte 3).toUInt64 <<< 24) |||
        ((buffer.byte 4).toUInt64 <<< 32) |||
        ((buffer.byte 5).toUInt64 <<< 40) |||
        ((buffer.byte 6).toUInt64 <<< 48) |||
        ((buffer.byte 7).toUInt64 <<< 56)
    .ok ({ marker := present }, present)
  else
    let _ := buffer.write (LazyCell.elementKey cell.tag) (borshUInt64 value)
    .ok ({ marker := value }, value)

@[pf_entry]
def optIsSome (_state : State) : UInt64 :=
  optCell.isSome

@[pf_entry]
def optGet (_state : State) : UInt64 :=
  optCell.getD 0

@[pf_entry]
def optSet (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let status := optCell.set value
  .ok ({ marker := status }, status)

@[pf_entry]
def optTake (_state : State) : Except Error (State × UInt64) :=
  let taken := optCell.takeD 0xcafebabecafebabe
  .ok ({ marker := taken }, taken)

end Examples.Near.NearLazy