import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Wasm.Near.Sdk.Store.Codec
import ProofForge.Wasm.Near.Sdk.Store.Iterable
import ProofForge.Wasm.Near.Sdk.Store.Vector

/-!
# Bounded direct NEAR sorted-vector TreeMap storage

`DirectTreeMap64` is a compiler-bounded, immediate-write subset of near-sdk-rs
`store::TreeMap<UInt64, UInt64>`: sorted ascending keys, `UInt64` values, capacity-bound
insertion. The durable layout composes the iterable-map namespaces:

* `P || 'm' || u64_le(key)` — lookup record (value `u64_le(value) || u32_le(index)`);
* `P || 'v' || u32_le(index)` — vector slot holding the sorted key at that index;
* logical length stays in the caller's ordinary `State` (like `DirectIterableMap64`).

Ordering: keys are kept sorted ascending by unsigned value. `put` replaces an existing key's
value in place, or appends at the tail — the new key must be strictly greater than the current
tail (no mid-vector shift in this bounded slice; out-of-order insertion fails closed with
`capacity + 1`). `remove` deletes the tail key only. All effects are immediate; no Rust
cache/flush/Drop timing, no generic K/V, no iterators, no heap rebalancing.

Callers must validate length and index codes before constructing mutation effects: an absent
lookup reads `capacity`; malformed lookup bytes read `capacity + 1`. Every base prefix must be
unique across collection instances and disjoint from raw and compiler state-field keys.
-/

namespace ProofForge.Wasm.Near.Sdk.Store

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk.Storage

/-- Compile-time capacity of a sorted TreeMap (1..64); prefix namespaces are derived from the
iterable `Prefix3` discipline. -/
abbrev DirectTreeMap64 := Nat

def DirectTreeMap64.wellFormed (map : DirectTreeMap64) : Bool :=
  iterableCapacityValid map 0

@[pf_inline] def DirectTreeMap64.bounded (capacity : Nat) : DirectTreeMap64 :=
  capacity

/-- The near-sdk-rs iterable namespaces for one TreeMap: map lookup tag `P || 'm'` and vector
tag `P || 'v'`. -/
@[pf_inline] def DirectTreeMap64.lookupTagOf (base : Prefix3) : Prefix4 :=
  base.lookupTag

@[pf_inline] def DirectTreeMap64.vectorTagOf (base : Prefix3) : Prefix4 :=
  base.vectorTag

/-- Lower bound slot for `key` over the sorted vector: reads the candidate slot and returns
its index when `candidate ≥ key`, else `length`. Single-slot primitive — the caller composes
the scan across its state loop (bounded by the compile-time capacity). -/
@[pf_inline] def DirectTreeMap64.slotAtLeast
    (capacity : DirectTreeMap64) (vectorTag : Prefix4) (index key : UInt64) : Bool :=
  let vector : DirectVector64 := capacity
  let candidate := DirectVector64.getD vector vectorTag 0 index 0
  candidate ≥ key

/-- Whether the key is present (has a lookup record with a valid index). -/
@[pf_inline] def DirectTreeMap64.has
    (capacity : DirectTreeMap64) (lookupTag : Prefix4) (key : UInt64) : UInt64 :=
  let map : DirectIterableMap64 := capacity
  let code := DirectIterableMap64.indexCode map lookupTag key
  if code < UInt64.ofNat capacity then 1 else 0

/-- Read the value for a present key, or `fallback`. -/
@[pf_inline] def DirectTreeMap64.getD
    (capacity : DirectTreeMap64) (lookupTag : Prefix4) (key fallback : UInt64) : UInt64 :=
  let map : DirectIterableMap64 := capacity
  DirectIterableMap64.getD map lookupTag key fallback

/-- Read the value at a sorted vector index, or `fallback` when out of range. -/
@[pf_inline] def DirectTreeMap64.keyAtD
    (capacity : DirectTreeMap64) (vectorTag : Prefix4) (length index fallback : UInt64) : UInt64 :=
  let map : DirectIterableMap64 := capacity
  DirectIterableMap64.keyAtD map vectorTag length index fallback

/-- Insert or replace: if the key exists, rewrite its lookup value (index unchanged). Otherwise
append at the sorted tail — `key` must be strictly greater than the current maximum (no
mid-vector shift in this bounded slice; out-of-order insertion fails closed with
`capacity + 1`). Returns the raw storage status of the final lookup write (0 insert, 1
replace). -/
@[pf_inline] def DirectTreeMap64.put
    (capacity : DirectTreeMap64) (lookupTag vectorTag : Prefix4)
    (length key value : UInt64) : UInt64 :=
  let map : DirectIterableMap64 := capacity
  let code := DirectIterableMap64.indexCode map lookupTag key
  if code < UInt64.ofNat capacity then
    -- present: rewrite the lookup value with the same index
    let result : ResultBuffer := 12
    let _ := result.write (map.lookupKey lookupTag key)
      (map.lookupValue value code)
    result.status
  else if length ≥ UInt64.ofNat capacity then
    UInt64.ofNat capacity + 1
  else if length > 0 then
    -- append path: the new key must sort strictly after the current tail
    let vector : DirectVector64 := capacity
    let tail := DirectVector64.getD vector vectorTag length (length - 1) 0
    if tail ≥ key then
      UInt64.ofNat capacity + 1
    else
      let slotResult : ResultBuffer := 8
      let _ := slotResult.write (vector.elementKey vectorTag length)
        (vector.elementValue key)
      let result : ResultBuffer := 12
      let _ := result.write (map.lookupKey lookupTag key)
        (map.lookupValue value length)
      result.status
  else
    -- empty map: first key goes to slot 0
    let vector : DirectVector64 := capacity
    let slotResult : ResultBuffer := 8
    let _ := slotResult.write (vector.elementKey vectorTag 0) (vector.elementValue key)
    let result : ResultBuffer := 12
    let _ := result.write (map.lookupKey lookupTag key)
      (map.lookupValue value 0)
    result.status

/-- Remove the LAST key (the tail slot). Middle-key removal requires a tail compaction pass
that this bounded slice does not express; removing a non-tail present key fails closed with
`capacity + 1`. Returns nearcore status 1 when the tail was removed, 0 when absent. -/
@[pf_inline] def DirectTreeMap64.remove
    (capacity : DirectTreeMap64) (lookupTag vectorTag : Prefix4)
    (length key : UInt64) : UInt64 :=
  let map : DirectIterableMap64 := capacity
  let code := DirectIterableMap64.indexCode map lookupTag key
  if code ≥ UInt64.ofNat capacity then 0
  else if code != length - 1 then
    UInt64.ofNat capacity + 1
  else
    let vector : DirectVector64 := capacity
    -- delete the lookup record and the tail vector slot
    let result : ResultBuffer := 12
    let _ := result.remove (map.lookupKey lookupTag key)
    let tailResult : ResultBuffer := 8
    let _ := tailResult.remove (vector.elementKey vectorTag (length - 1))
    result.status

/-- Source-level TreeMap handle: compile-time capacity + derived namespaces. -/
structure DirectTreeMap64.Handle where
  capacity : DirectTreeMap64
  vectorTag : Prefix4
  lookupTag : Prefix4
  deriving Repr

@[pf_inline] def DirectTreeMap64.handle
    (capacity : Nat) (base : Prefix3) : DirectTreeMap64.Handle :=
  { capacity := capacity
    vectorTag := base.vectorTag
    lookupTag := base.lookupTag }

/-- The iterable-map lookup key `P || 'm' || u64_le(key)` for direct fixture use. Built
directly (no delegation) so a single `unfoldUserHelper` pass resolves it. -/
@[pf_inline] def DirectTreeMap64.Handle.lookupKey
    (h : DirectTreeMap64.Handle) (key : UInt64) : BoundedBytes 12 :=
  let p := UInt64.ofNat h.capacity
  let m := p * 0x1000000 + 0x6d  -- base || 'm'
  let k := key
  { length := 12
    values := #v[
      (k &&& 0xff).toUInt8,
      ((k >>> 8) &&& 0xff).toUInt8,
      ((k >>> 16) &&& 0xff).toUInt8,
      ((k >>> 24) &&& 0xff).toUInt8,
      ((k >>> 32) &&& 0xff).toUInt8,
      ((k >>> 40) &&& 0xff).toUInt8,
      ((k >>> 48) &&& 0xff).toUInt8,
      ((k >>> 56) &&& 0xff).toUInt8,
      (m &&& 0xff).toUInt8,
      ((m >>> 8) &&& 0xff).toUInt8,
      ((m >>> 16) &&& 0xff).toUInt8,
      ((m >>> 24) &&& 0xff).toUInt8
    ] }

/-- The iterable-map lookup value `u64_le(value) || u32_le(index)` for direct fixture use. -/
@[pf_inline] def DirectTreeMap64.Handle.lookupValue
    (h : DirectTreeMap64.Handle) (value index : UInt64) : BoundedBytes 12 :=
  { length := 12
    values := #v[
      (value &&& 0xff).toUInt8,
      ((value >>> 8) &&& 0xff).toUInt8,
      ((value >>> 16) &&& 0xff).toUInt8,
      ((value >>> 24) &&& 0xff).toUInt8,
      ((value >>> 32) &&& 0xff).toUInt8,
      ((value >>> 40) &&& 0xff).toUInt8,
      ((value >>> 48) &&& 0xff).toUInt8,
      ((value >>> 56) &&& 0xff).toUInt8,
      (index &&& 0xff).toUInt8,
      ((index >>> 8) &&& 0xff).toUInt8,
      ((index >>> 16) &&& 0xff).toUInt8,
      ((index >>> 24) &&& 0xff).toUInt8
    ] }

/-- The sorted-vector slot key `P || 'v' || u32_le(index)` for direct fixture use. -/
@[pf_inline] def DirectTreeMap64.Handle.elementKey
    (h : DirectTreeMap64.Handle) (index : UInt64) : BoundedBytes 8 :=
  let p := UInt64.ofNat h.capacity
  let v := p * 0x1000000 + 0x76  -- base || 'v'
  { length := 8
    values := #v[
      (v &&& 0xff).toUInt8,
      ((v >>> 8) &&& 0xff).toUInt8,
      ((v >>> 16) &&& 0xff).toUInt8,
      ((v >>> 24) &&& 0xff).toUInt8,
      (index &&& 0xff).toUInt8,
      ((index >>> 8) &&& 0xff).toUInt8,
      ((index >>> 16) &&& 0xff).toUInt8,
      ((index >>> 24) &&& 0xff).toUInt8
    ] }

/-- The sorted-vector slot value (standalone Borsh `UInt64`). -/
@[pf_inline] def DirectTreeMap64.Handle.elementValue
    (h : DirectTreeMap64.Handle) (value : UInt64) : BoundedBytes 8 :=
  DirectVector64.elementValue h.capacity value

@[pf_inline] def DirectTreeMap64.Handle.has
    (h : DirectTreeMap64.Handle) (key : UInt64) : UInt64 :=
  DirectTreeMap64.has h.capacity h.lookupTag key

@[pf_inline] def DirectTreeMap64.Handle.getD
    (h : DirectTreeMap64.Handle) (key fallback : UInt64) : UInt64 :=
  DirectTreeMap64.getD h.capacity h.lookupTag key fallback

@[pf_inline] def DirectTreeMap64.Handle.keyAtD
    (h : DirectTreeMap64.Handle) (length index fallback : UInt64) : UInt64 :=
  DirectTreeMap64.keyAtD h.capacity h.vectorTag length index fallback

@[pf_inline] def DirectTreeMap64.Handle.put
    (h : DirectTreeMap64.Handle) (length key value : UInt64) : UInt64 :=
  DirectTreeMap64.put h.capacity h.lookupTag h.vectorTag length key value

@[pf_inline] def DirectTreeMap64.Handle.remove
    (h : DirectTreeMap64.Handle) (length key : UInt64) : UInt64 :=
  DirectTreeMap64.remove h.capacity h.lookupTag h.vectorTag length key

end ProofForge.Wasm.Near.Sdk.Store