/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Pair-row contractions of exact-size Boolean moments

An exact-size moment functional through degree four allows the constant and
singleton Gram rows to be replaced by sums of pair rows against every
monomial of degree at most two.
-/
namespace ProximityGap.PaleyQuarticSliceContractions

variable {I : Type*} [Fintype I] [DecidableEq I] (y : Finset I → ℝ) (k : ℝ)

/-- Boolean multiplication is represented by inserting an index in a finite set. -/
def ExactSlice : Prop :=
  ∀ T : Finset I, T.card ≤ 3 → (∑ j : I, y (insert j T)) = k * y T

/-- Sum of the pair rows incident to a vertex, evaluated against a monomial. -/
theorem star_contraction (hs : ExactSlice y k) (i : I) (T : Finset I) (hT : T.card ≤ 2) :
    ∑ j ∈ Finset.univ.erase i, y (insert j (insert i T)) = (k-1) * y (insert i T) := by
  have ht : (insert i T).card ≤ 3 :=
    (Finset.card_insert_le i T).trans (Nat.succ_le_succ hT)
  have he := Finset.sum_erase_add (s := (Finset.univ : Finset I))
    (f := fun j => y (insert j (insert i T))) (Finset.mem_univ i)
  rw [hs _ ht] at he
  simp only [Finset.insert_idem] at he
  linarith

/-- The sum over all ordered distinct pairs recovers the constant Gram row. -/
theorem all_pairs_contraction (hs : ExactSlice y k) (T : Finset I) (hT : T.card ≤ 2) :
    ∑ i : I, ∑ j ∈ Finset.univ.erase i, y (insert j (insert i T)) =
      k * (k-1) * y T := by
  simp_rw [star_contraction y k hs _ T hT]
  rw [← Finset.mul_sum, hs T (hT.trans (by decide))]
  ring

#print axioms star_contraction
#print axioms all_pairs_contraction

end ProximityGap.PaleyQuarticSliceContractions
