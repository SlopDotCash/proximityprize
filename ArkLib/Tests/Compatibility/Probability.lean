/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/

import ArkLib.ToVCVio.Lemmas

/-!
# Probability compatibility acceptance clients

An optional failure loses all successful-output mass. A base oracle computation returning
`none` succeeds with that value instead. The bind client fixes both monads explicitly so a
coercion or a missing discrete-support instance cannot silently switch these observations.
-/

namespace ArkLibTest.Compatibility.Probability

/-- Optional failure has total failure mass. -/
theorem optional_failure_mass_one :
    probFailure (m := OptionT ProbComp) (failure : OptionT ProbComp Nat) = 1 := by
  simp [probFailure]

/-- Returning `none` in the base monad is a successful output. -/
theorem base_none_failure_mass_zero :
    probFailure (m := ProbComp) (pure none : ProbComp (Option Nat)) = 0 := by
  simp [probFailure]

/-- A native probabilistic prefix and optional continuations use the proved discrete-support
instance when checking losslessness after wrapping the whole bind. -/
theorem optional_bind_lossless (mx : ProbComp Nat) (my : Nat → ProbComp (Option Nat)) :
    prFail (m := OptionT ProbComp) (OptionT.mk (mx >>= my)) = 0 ↔
      prFail (m := ProbComp) mx = 0 ∧
        ∀ x ∈ support mx, prFail (m := OptionT ProbComp) (OptionT.mk (my x)) = 0 :=
  OptionT.probFailure_mk_bind_eq_zero_iff (m := ProbComp) mx my

#print axioms optional_failure_mass_one
#print axioms base_none_failure_mass_zero
#print axioms optional_bind_lossless

end ArkLibTest.Compatibility.Probability
