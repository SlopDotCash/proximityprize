/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Inner products of centered agreement sets -/

namespace ProximityGap.CenteredAgreement

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A centered indicator scaled so that its inner products clear the domain denominator. -/
noncomputable def entry (t : ℕ) (A : Finset I) (x : I) : ℝ :=
  ((if x ∈ A then (Fintype.card I : ℝ) else 0) - t) / Real.sqrt (Fintype.card I)

private def mark (A : Finset I) (x : I) : ℝ := if x ∈ A then 1 else 0

private theorem sum_mark (A : Finset I) : ∑ x, mark A x = A.card := by
  unfold mark
  rw [Finset.sum_boole]
  have h : Finset.univ.filter (fun x => x ∈ A) = A := by ext; simp
  rw [h]

variable [Nonempty I]

/-- Centering removes the product of the two set sizes from the scaled intersection. -/
theorem dot_eq (A B : Finset I) (t : ℕ) (ha : A.card = t) (hb : B.card = t) :
    ∑ x, entry t A x * entry t B x =
      (Fintype.card I : ℝ) * (A ∩ B).card - (t : ℝ) ^ 2 := by
  have hn : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hterm (x : I) : entry t A x * entry t B x =
      (Fintype.card I : ℝ) * mark (A ∩ B) x - t * mark A x - t * mark B x +
        (t : ℝ) ^ 2 / Fintype.card I := by
    simp only [entry, div_mul_div_comm, ← sq, Real.sq_sqrt hn.le, mark, Finset.mem_inter]
    by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
      simp only [hA, hB, and_true, and_false, ↓reduceIte] <;> field_simp <;> ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_mark, ha, hb, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- The common squared norm for agreement sets of cardinality `t`. -/
theorem sum_sq_eq (A : Finset I) (t : ℕ) (ha : A.card = t) :
    ∑ x, (entry t A x) ^ 2 = (Fintype.card I : ℝ) * t - (t : ℝ) ^ 2 := by
  simpa only [sq, Finset.inter_self, ha] using dot_eq A A t ha ha

#print axioms dot_eq
#print axioms sum_sq_eq

end ProximityGap.CenteredAgreement
