import ProofForge
import Examples.Counter
import Examples.TokenShape

/-!
# Kernel-proof connectivity checks

Authoritative proofs live in the contract files (`Examples/Counter.lean`,
`Examples/TokenShape.lean`). This file spot-checks theorems on concrete values and
the NEAR SDK capability surface so the test plane stays wired after signature drift.
-/

namespace Tests.ProofSpec

open Examples.Counter

#guard
  match increment ({ value := 2 } : State) 3 with
  | .ok (t, ret) => t.value == 5 && ret == 5
  | .error _ => false

#guard
  match decrement ({ value := 2 } : State) 5 with
  | .error .overflow => true
  | .ok _ => false

example (s : State) (d : UInt64) (t : State) (r : UInt64)
    (h : increment s d = .ok (t, r)) : r = t.value :=
  (increment_ok s d h).2

private def nearA : ProofForge.Wasm.Near.Runtime.AccountId :=
  { length := 9, w0 := 1, w1 := 2, w2 := 0, w3 := 0, w4 := 0,
    w5 := 0, w6 := 0, w7 := 0 }

private def nearB : ProofForge.Wasm.Near.Runtime.AccountId :=
  { nearA with w7 := 3 }

#guard ProofForge.Wasm.Near.Sdk.AccountId.eq nearA nearA
#guard !ProofForge.Wasm.Near.Sdk.AccountId.eq nearA nearB
#guard ({ w0 := 0, w1 := 0 } : ProofForge.Core.Value.UInt128) == ⟨0, 0⟩
#guard ({ w0 := 1, w1 := 2 } : ProofForge.Wasm.Near.Runtime.NearToken).w1 == 2
#guard ProofForge.Wasm.Near.Runtime.nearTokenAddOk 0 0 0 0 == 0
#guard ProofForge.Wasm.Near.Runtime.nearTokenSubOk 1 0 0 0 == 0


example (s : Examples.TokenShape.State) (a : UInt64)
    (h : Examples.TokenShape.credit s a = .error .overflow) :
    ¬ ∃ t r, Examples.TokenShape.credit s a = .ok (t, r) :=
  Examples.TokenShape.credit_overflow_not_ok s a h

end Tests.ProofSpec
