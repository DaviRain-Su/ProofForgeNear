import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Wasm.Near.Sdk.Store.Codec

/-!
# Bounded direct NEAR Lazy and LazyOption single-value cells

This is the fixed-width `UInt64` subset of current near-sdk-rs `store::Lazy` and
`store::LazyOption`:

* cell key: the bare four-byte compile-time prefix (no index suffix);
* `Lazy` cell value: standalone Borsh `UInt64` (exactly eight little-endian bytes);
* `LazyOption` cell value: the same standalone Borsh `UInt64`, with absence carried by
  the raw-storage key itself (no Borsh option discriminant byte).

The caller owns namespace separation between every cell, collection, raw key, and compiler
state-field key. Both cells write immediately: durable bytes match the Rust layouts, but the
mutation timing does not model Rust cache/`Drop`-flush behavior, and same-invocation raw reads
observe the write (like the direct collections). Neither type provides generic codecs, borrows,
references, or the `T: BorshSerialize` generic surface.
-/

namespace ProofForge.Wasm.Near.Sdk.Store

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk.Storage

/-- Compile-time four-byte namespace for one lazy `UInt64` cell. -/
abbrev LazyCell := Prefix4

def LazyCell.wellFormed (cell : LazyCell) : Bool :=
  Prefix4.wellFormed cell

@[pf_inline] def LazyCell.bounded (tag : Nat) : LazyCell :=
  tag

/-- The bare four-byte little-endian prefix as a storage key (no suffix). -/
@[pf_inline] def LazyCell.elementKey (cell : LazyCell) : BoundedBytes 4 :=
  let p := UInt64.ofNat cell
  { length := 4
    values := #v[
      (p &&& 0xff).toUInt8,
      ((p >>> 8) &&& 0xff).toUInt8,
      ((p >>> 16) &&& 0xff).toUInt8,
      ((p >>> 24) &&& 0xff).toUInt8
    ] }

/-- near-sdk-rs `store::Lazy`: the standalone Borsh `UInt64` value encoding. -/
@[pf_inline] def LazyCell.elementValue (value : UInt64) : BoundedBytes 8 :=
  borshUInt64 value

/-- Read and decode the cell, or return `fallback` for absence or malformed storage.
Unlike Rust `Lazy.get`, this observes durable storage directly and performs no write. -/
@[pf_inline] def LazyCell.getD (cell : LazyCell) (fallback : UInt64) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.read cell.elementKey
  resultUInt64D fallback

/-- Immediately overwrite the cell, returning nearcore status 0 for insert or 1 for
replacement. -/
@[pf_inline] def LazyCell.set (cell : LazyCell) (value : UInt64) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.write cell.elementKey (LazyCell.elementValue value)
  result.status

/-- Read-or-initialize: an absent cell is initialized to `value` (status 0) and `value` is
returned; a present cell returns its decoded value (or `fallback` when malformed) without
writing. Malformed storage therefore never traps but never initializes either. -/
@[pf_inline] def LazyCell.getOrSetD (cell : LazyCell) (fallback value : UInt64) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.read cell.elementKey
  if result.status == 1 then resultUInt64D fallback
  else
    let _ := result.write cell.elementKey (LazyCell.elementValue value)
    value

/-- Compile-time four-byte namespace for one optional lazy `UInt64` cell. -/
abbrev LazyOptionCell := Prefix4

def LazyOptionCell.wellFormed (cell : LazyOptionCell) : Bool :=
  Prefix4.wellFormed cell

@[pf_inline] def LazyOptionCell.bounded (tag : Nat) : LazyOptionCell :=
  tag

@[pf_inline] def LazyOptionCell.elementKey (cell : LazyOptionCell) : BoundedBytes 4 :=
  LazyCell.elementKey cell

/-- `Some`-equivalent: the standalone Borsh `UInt64` value encoding. Absence is carried by the
missing storage key, not a Borsh discriminant (Rust `LazyOption` stores `Some` values the same
way; `None` means "never written"). -/
@[pf_inline] def LazyOptionCell.elementValue (value : UInt64) : BoundedBytes 8 :=
  borshUInt64 value

/-- Whether the optional cell holds a value (nearcore status 1) or is `None` (status 0). -/
@[pf_inline] def LazyOptionCell.isSome (cell : LazyOptionCell) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.hasKey cell.elementKey
  result.status

/-- Read and decode the present cell, or return `fallback` when absent or malformed. -/
@[pf_inline] def LazyOptionCell.getD (cell : LazyOptionCell) (fallback : UInt64) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.read cell.elementKey
  resultUInt64D fallback

/-- Immediately store `Some value`, returning nearcore status 0 for insert or 1 for
replacement. -/
@[pf_inline] def LazyOptionCell.set (cell : LazyOptionCell) (value : UInt64) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.write cell.elementKey (LazyOptionCell.elementValue value)
  result.status

/-- `take()`: remove and return the previous value when present, or `fallback` when absent.
The removed bytes are reclaimed immediately. -/
@[pf_inline] def LazyOptionCell.takeD (cell : LazyOptionCell) (fallback : UInt64) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.read cell.elementKey
  let taken := resultUInt64D fallback
  let _ := result.remove cell.elementKey
  taken

/-- Source handle for a lazy cell namespace: compile-time `Prefix4` only. Methods are
`@[pf_inline]` facades so Extract erases to raw cell ops. -/
structure LazyCell.Handle where
  tag : LazyCell
  deriving Repr

@[pf_inline] def LazyCell.handle (tag : Nat) : LazyCell.Handle :=
  { tag := tag }

@[pf_inline] def LazyCell.Handle.getD (h : LazyCell.Handle) (fallback : UInt64) : UInt64 :=
  LazyCell.getD h.tag fallback

@[pf_inline] def LazyCell.Handle.set (h : LazyCell.Handle) (value : UInt64) : UInt64 :=
  LazyCell.set h.tag value

@[pf_inline] def LazyCell.Handle.getOrSetD
    (h : LazyCell.Handle) (fallback value : UInt64) : UInt64 :=
  LazyCell.getOrSetD h.tag fallback value

/-- Source handle for an optional lazy cell namespace: compile-time `Prefix4` only. -/
structure LazyOptionCell.Handle where
  tag : LazyOptionCell
  deriving Repr

@[pf_inline] def LazyOptionCell.handle (tag : Nat) : LazyOptionCell.Handle :=
  { tag := tag }

@[pf_inline] def LazyOptionCell.Handle.isSome (h : LazyOptionCell.Handle) : UInt64 :=
  LazyOptionCell.isSome h.tag

@[pf_inline] def LazyOptionCell.Handle.getD
    (h : LazyOptionCell.Handle) (fallback : UInt64) : UInt64 :=
  LazyOptionCell.getD h.tag fallback

@[pf_inline] def LazyOptionCell.Handle.set (h : LazyOptionCell.Handle) (value : UInt64) : UInt64 :=
  LazyOptionCell.set h.tag value

@[pf_inline] def LazyOptionCell.Handle.takeD
    (h : LazyOptionCell.Handle) (fallback : UInt64) : UInt64 :=
  LazyOptionCell.takeD h.tag fallback

end ProofForge.Wasm.Near.Sdk.Store