import ProofForge

namespace Examples.Near.NearTreeMap
open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk.Storage
open ProofForge.Wasm.Near.Sdk.Store

structure State where
  marker : UInt64
  length : UInt64
  pendingKey : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- T3: capacity 3, base prefix `TRM1` (`0x314d5254`). -/
@[pf_inline] def slots : DirectTreeMap64.Handle :=
  DirectTreeMap64.handle 3 0x314d5254

@[pf_entry]
def init (seed : UInt64) : State :=
  { marker := seed, length := 0, pendingKey := 0 }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.length

@[pf_entry]
def has (_state : State) (key : UInt64) : UInt64 :=
  let result : ResultBuffer := 12
  let _ := result.read (slots.lookupKey key)
  if result.status = 1 then 1 else 0

@[pf_entry]
def getValue (_state : State) (key : UInt64) : UInt64 :=
  let result : ResultBuffer := 12
  let _ := result.read (slots.lookupKey key)
  if result.status = 1 then
    if result.fits then
      if result.length = 12 then
        (result.byte 0).toUInt64 |||
          ((result.byte 1).toUInt64 <<< 8) |||
          ((result.byte 2).toUInt64 <<< 16) |||
          ((result.byte 3).toUInt64 <<< 24) |||
          ((result.byte 4).toUInt64 <<< 32) |||
          ((result.byte 5).toUInt64 <<< 40) |||
          ((result.byte 6).toUInt64 <<< 48) |||
          ((result.byte 7).toUInt64 <<< 56)
      else 0
    else 0
  else 0

/-- Ordered read: the key at sorted vector index `index`, or 0 when out of range. -/
@[pf_entry]
def keyAt (_state : State) (index : UInt64) : UInt64 :=
  if index < _state.length then
    let result : ResultBuffer := 8
    let _ := result.read (slots.elementKey index)
    if result.status = 1 then
      (result.byte 0).toUInt64 |||
        ((result.byte 1).toUInt64 <<< 8) |||
        ((result.byte 2).toUInt64 <<< 16) |||
        ((result.byte 3).toUInt64 <<< 24) |||
        ((result.byte 4).toUInt64 <<< 32) |||
        ((result.byte 5).toUInt64 <<< 40) |||
        ((result.byte 6).toUInt64 <<< 48) |||
        ((result.byte 7).toUInt64 <<< 56)
    else 0
  else 0

/-- Phase 1 of the two-phase put: stage the key. -/
@[pf_entry]
def putKey (state : State) (key : UInt64) : Except Error (State × UInt64) :=
  if key = 0 then
    .error .overflow
  else
    .ok ({ state with pendingKey := key }, key)

/-- Phase 2 of the two-phase put: commit `pendingKey → value`. In-order append only;
duplicate keys fail closed (v0 has no lookup rewrite path for a present tail key).
All storage ops are explicit (iterable-map recipe). -/
@[pf_entry]
def putValue (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let key := state.pendingKey
  if key = 0 then
    .error .overflow
  else
    let lookupResult : ResultBuffer := 12
    let _ := lookupResult.read (slots.lookupKey key)
    if lookupResult.status = 1 then
      .error .overflow
    else if state.length >= 3 then
      .error .overflow
    else if state.length = 0 then
      let slotResult : ResultBuffer := 8
      let _ := slotResult.write (slots.elementKey 0) (slots.elementValue key)
      let result : ResultBuffer := 12
      let _ := result.write (slots.lookupKey key) (slots.lookupValue value 0)
      .ok ({ marker := 0, length := 1, pendingKey := 0 }, 0)
    else
      let vectorResult : ResultBuffer := 8
      let _ := vectorResult.read (slots.elementKey (state.length - 1))
      if vectorResult.status = 1 then
        if vectorResult.length = 8 then
          let tail :=
            (vectorResult.byte 0).toUInt64 |||
              ((vectorResult.byte 1).toUInt64 <<< 8) |||
              ((vectorResult.byte 2).toUInt64 <<< 16) |||
              ((vectorResult.byte 3).toUInt64 <<< 24) |||
              ((vectorResult.byte 4).toUInt64 <<< 32) |||
              ((vectorResult.byte 5).toUInt64 <<< 40) |||
              ((vectorResult.byte 6).toUInt64 <<< 48) |||
              ((vectorResult.byte 7).toUInt64 <<< 56)
          if tail >= key then
            .error .overflow
          else
            let slotResult : ResultBuffer := 8
            let _ := slotResult.write (slots.elementKey state.length)
              (slots.elementValue key)
            let result : ResultBuffer := 12
            let _ := result.write (slots.lookupKey key)
              (slots.lookupValue value state.length)
            .ok ({ marker := state.length, length := state.length + 1, pendingKey := 0 },
              state.length)
        else
          .error .overflow
      else
        .error .overflow

/-- Remove the tail key (the largest); middle-key removal fails closed. Storage ops are
explicit (iterable-map recipe). -/
@[pf_entry]
def removeTail (state : State) (key : UInt64) : Except Error (State × UInt64) :=
  let lookupResult : ResultBuffer := 12
  let _ := lookupResult.read (slots.lookupKey key)
  if lookupResult.status = 1 then
    if lookupResult.length = 12 then
      let index :=
        (lookupResult.byte 8).toUInt64 |||
          ((lookupResult.byte 9).toUInt64 <<< 8) |||
          ((lookupResult.byte 10).toUInt64 <<< 16) |||
          ((lookupResult.byte 11).toUInt64 <<< 24)
      if index = state.length - 1 then
        let result : ResultBuffer := 12
        let _ := result.remove (slots.lookupKey key)
        let tailResult : ResultBuffer := 8
        let _ := tailResult.remove (slots.elementKey (state.length - 1))
        .ok ({ marker := index, length := state.length - 1, pendingKey := 0 }, index)
      else
        .error .overflow
    else
      .error .overflow
  else
    .ok ({ state with marker := 0 }, 0)

end Examples.Near.NearTreeMap