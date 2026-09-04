import Examples.Near.NearBorshRecord
import Lean
import ProofForge

/-! Borsh record output (result_serializer for u64-field structs) — codec-level invariants.
The extraction-surface half (fixture with a mutating method returning the record) is deferred:
plain user boundary records in mutating returns need kind-classification support that lands
with the split-key STATE lifecycle. The codec + emitter arms here are pinned so the wire
policy cannot drift before that lands. -/

namespace Tests.NearBorshRecordSpec

open Lean Elab Command
open ProofForge.Wasm.Near
open ProofForge.Core.Codec

private def fields2 : Array (String × Schema) :=
  #[("total", Schema.scalar Scalar.uint64), ("version", Schema.scalar Scalar.uint64)]

#guard match Codec.targetOutputPlan
    (.record "Examples.Near.NearBorshRecord.Summary" fields2) with
  | .ok (.borshRecord 2) => true
  | _ => false

private def fields8 : Array (String × Schema) :=
  #[("a", Schema.scalar Scalar.uint64), ("b", Schema.scalar Scalar.uint64),
    ("c", Schema.scalar Scalar.uint64), ("d", Schema.scalar Scalar.uint64),
    ("e", Schema.scalar Scalar.uint64), ("f", Schema.scalar Scalar.uint64),
    ("g", Schema.scalar Scalar.uint64), ("h", Schema.scalar Scalar.uint64)]

#guard match Codec.targetOutputPlan (.record "R" fields8) with
  | .ok (.borshRecord 8) => true
  | _ => false

private def fieldsBad : Array (String × Schema) :=
  #[("a", Schema.scalar Scalar.uint64), ("b", Schema.scalar Scalar.uint128)]

#guard match Codec.targetOutputPlan (.record "R" fieldsBad) with
  | .error _ => true
  | _ => false

#guard match Codec.targetOutputPlan (.record "R" (Array.mk ([] : List (String × Schema)))) with
  | .error _ => true
  | _ => false

private def fields9 : Array (String × Schema) :=
  (Array.range 9).map fun i => (s!"f{i}", Schema.scalar Scalar.uint64)

#guard match Codec.targetOutputPlan (.record "R" fields9) with
  | .error _ => true
  | _ => false

-- Known record schemas keep their dedicated JSON policies (no borsh-record takeover).
#guard match Codec.targetOutputPlan Codec.storageBalanceResultSchema with
  | .ok .jsonStorageBalanceOption => true
  | _ => false

private def bytesPlanIsBorsh : Codec.OutputPlan :=
  match Codec.targetOutputPlan (.boundedBytes 32) with
  | .ok plan => plan
  | .error _ => .voidEmpty

#guard bytesPlanIsBorsh == Codec.OutputPlan.borsh
    { kind := Codec.BorshOutputKind.bytes, capacity := 32, elementWidth := 1,
      validateUtf8 := false }

#guard (Codec.OutputPlan.borshRecord 3).canonical ==
  "near-borsh-record-u64-v1(fields=3)"

#guard (Codec.OutputPlan.borshRecord 3).sourceValueCount == 3

end Tests.NearBorshRecordSpec