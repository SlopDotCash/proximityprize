/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Convex.StrictConvexSpace

/-!
# Door (iv): the MULTI-piece coherence saturation CONVERSE — `ρ = 1 ⟹ pairwise same-ray`

`_DoorIVComplexRayCoherence.lean` establishes, for a strictly convex real normed space, the SHARP
two-piece criterion `twoPieceNormCoherence x y = 1 ↔ SameRay ℝ x y`, and (separately) the FORWARD
multi-piece direction `multiPieceNormCoherence_eq_one_of_common_nonneg_ray` (all pieces on one
common nonnegative ray ⟹ `ρ = 1`).

What that file LEAVES OPEN is the multi-piece **converse**: does coherence saturation `ρ = 1` for
finitely many pieces FORCE the pieces to be pairwise same-ray?  The forward lemma only certifies
saturation when the pieces are presented *already collinear* (a common `u` with nonnegative scalars);
it does not rule out a saturating configuration that is geometrically more general.  Without the
converse the multi-piece obstruction is one-sided: it says common-ray pieces saturate, but not that
saturation is *equivalent* to alignment.

This file closes that gap.  In a strictly convex space, norm-additivity of a finite sum
`‖∑ A i‖ = ∑ ‖A i‖` forces every PAIR of pieces to be `SameRay` (proved by `Finset` induction off
the Mathlib two-vector `sameRay_iff_norm_add` together with `SameRay.add_left`/`add_right`).  Hence:

> **Multi-piece coherence saturation `ρ = 1` ⟺ the pieces are pairwise same-ray.**

Consequence for door (iv): the multi-piece obstruction is now TWO-sided and sharp.  Any multi-piece
refinement of the worst-frequency monomial sum that claims a strict coherence drop `ρ < 1` MUST
exhibit at least one genuinely non-collinear PAIR among its pieces — subdivision into more (or
cleverer) real/complex pieces contributes nothing unless it produces a non-same-ray pair.  This is a
pure triangle-equality / strict-convexity bookkeeping result: no Gauss-period cancellation, no
moment, no completion, no anti-concentration is claimed or used.  It strengthens the constraint that
any door-(iv) anti-concentration certificate must satisfy.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ProximityGap.Frontier.DoorIVMultiPieceSameRayConverse

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]

/-- Normalized norm coherence of finitely many vector pieces (matches the definition used in
`_DoorIVComplexRayCoherence`). -/
noncomputable def multiPieceNormCoherence {ι : Type*} (s : Finset ι) (A : ι → E) : ℝ :=
  ‖∑ i ∈ s, A i‖ / (∑ i ∈ s, ‖A i‖)

/-- **Key geometric lemma.** In a strictly convex space, if a finite family of vectors has
norm-additive sum (`‖∑ A i‖ = ∑ ‖A i‖`), then EVERY piece is `SameRay` with the running partial
sum that excludes it; concretely every piece is same-ray with the TOTAL sum.  This is the engine for
the pairwise statement. -/
theorem sameRay_piece_total_of_norm_sum_eq {ι : Type*} (s : Finset ι) (A : ι → E)
    (hnorm : ‖∑ i ∈ s, A i‖ = ∑ i ∈ s, ‖A i‖) :
    ∀ j ∈ s, SameRay ℝ (A j) (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction with
  | empty => intro j hj; simp at hj
  | insert a t ha ih =>
    -- Split the sum: ∑_{insert a t} = A a + ∑_t
    have hsum_split : ∑ i ∈ insert a t, A i = A a + ∑ i ∈ t, A i := by
      rw [Finset.sum_insert ha]
    have hnorm_split : ∑ i ∈ insert a t, ‖A i‖ = ‖A a‖ + ∑ i ∈ t, ‖A i‖ := by
      rw [Finset.sum_insert ha]
    -- Norm-additivity on the split: ‖A a + ∑_t‖ = ‖A a‖ + ∑_t ‖A i‖
    have hadd : ‖A a + ∑ i ∈ t, A i‖ = ‖A a‖ + ∑ i ∈ t, ‖A i‖ := by
      rw [← hsum_split, ← hnorm_split]; exact hnorm
    -- The triangle inequality is tight, and ‖A a‖ + ∑_t‖A i‖ ≥ ‖A a‖ + ‖∑_t‖ ≥ ‖A a + ∑_t‖,
    -- so both the inner (∑_t) and outer triangle equalities must be tight.
    have htri_inner : ‖∑ i ∈ t, A i‖ ≤ ∑ i ∈ t, ‖A i‖ := norm_sum_le _ _
    have htri_outer : ‖A a + ∑ i ∈ t, A i‖ ≤ ‖A a‖ + ‖∑ i ∈ t, A i‖ := norm_add_le _ _
    -- From hadd and the two triangle inequalities, force both tight.
    -- ‖A a‖ + ∑_t ‖A i‖ = ‖A a + ∑_t‖ ≤ ‖A a‖ + ‖∑_t‖ ≤ ‖A a‖ + ∑_t ‖A i‖
    have houter_eq : ‖A a + ∑ i ∈ t, A i‖ = ‖A a‖ + ‖∑ i ∈ t, A i‖ := by
      have h1 : ‖A a‖ + ∑ i ∈ t, ‖A i‖ ≤ ‖A a‖ + ‖∑ i ∈ t, A i‖ := by
        rw [hadd] at *; linarith [htri_outer]
      have h2 : ‖∑ i ∈ t, ‖A i‖‖ = ∑ i ∈ t, ‖A i‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
      -- ∑_t ‖A i‖ ≤ ‖∑_t‖ combined with htri_inner gives equality
      have hinner_ge : ∑ i ∈ t, ‖A i‖ ≤ ‖∑ i ∈ t, A i‖ := by linarith
      have hinner_eq : ‖∑ i ∈ t, A i‖ = ∑ i ∈ t, ‖A i‖ := le_antisymm htri_inner hinner_ge
      rw [hadd, hinner_eq]
    have hinner_eq : ‖∑ i ∈ t, A i‖ = ∑ i ∈ t, ‖A i‖ := by
      -- from houter_eq and hadd
      have : ‖A a‖ + ‖∑ i ∈ t, A i‖ = ‖A a‖ + ∑ i ∈ t, ‖A i‖ := by
        rw [← houter_eq, hadd]
      linarith
    -- A a is same-ray with ∑_t (two-vector tight triangle)
    have hray_a_t : SameRay ℝ (A a) (∑ i ∈ t, A i) :=
      (sameRay_iff_norm_add).mpr houter_eq
    -- recursion hypothesis on t
    have ih_t : ∀ j ∈ t, SameRay ℝ (A j) (∑ i ∈ t, A i) := ih hinner_eq
    -- Now prove the goal for every j ∈ insert a t, target = A a + ∑_t
    intro j hj
    rw [hsum_split]
    rcases Finset.mem_insert.mp hj with hja | hjt
    · subst hja
      -- A a same-ray with A a + ∑_t : since A a is same-ray with ∑_t, it's same-ray with the sum
      exact SameRay.add_right (SameRay.rfl) hray_a_t
    · -- A j (j ∈ t) same-ray with A a + ∑_t
      -- A j same-ray ∑_t (ih), and A a same-ray ∑_t (hray_a_t) ⟹ A j same-ray A a (need care)
      -- Instead: A j same-ray ∑_t, and ∑_t = (A a + ∑_t) - A a ... use add_right with A j ~ A a, A j ~ ∑_t
      have hj_t : SameRay ℝ (A j) (∑ i ∈ t, A i) := ih_t j hjt
      -- A j same-ray A a: from A j ~ ∑_t and A a ~ ∑_t.  Use the partial-sum trick:
      -- ‖A a + ∑_t‖ = ‖A a‖ + ‖∑_t‖ AND A j contributes to ∑_t additively.
      -- Cleanest: show A j ~ (A a + ∑_t) directly via add_right needing A j ~ A a and A j ~ ∑_t.
      have hj_a : SameRay ℝ (A j) (A a) := by
        -- both A j and A a are same-ray with ∑_t; if ∑_t ≠ 0 they share its ray; handle ∑_t = 0.
        by_cases hzt : (∑ i ∈ t, A i) = 0
        · -- ∑_t = 0 with ∑_t ‖A i‖ = ‖∑_t‖ = 0 forces every ‖A i‖ = 0 for i ∈ t, so A j = 0.
          have hsum0 : ∑ i ∈ t, ‖A i‖ = 0 := by rw [← hinner_eq, hzt, norm_zero]
          have hAj0 : ‖A j‖ = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => norm_nonneg _)).mp hsum0 j hjt
          have : A j = 0 := norm_eq_zero.mp hAj0
          rw [this]; exact SameRay.zero_left _
        · exact SameRay.trans hj_t (hray_a_t.symm) (fun h => absurd h hzt)
      exact SameRay.add_right hj_a hj_t

/-- **Multi-piece pairwise same-ray converse.** In a strictly convex space, if the finite family `A`
on `s` has norm-additive sum then every pair of pieces is `SameRay`. -/
theorem pairwise_sameRay_of_norm_sum_eq {ι : Type*} (s : Finset ι) (A : ι → E)
    (hnorm : ‖∑ i ∈ s, A i‖ = ∑ i ∈ s, ‖A i‖) :
    ∀ j ∈ s, ∀ k ∈ s, SameRay ℝ (A j) (A k) := by
  classical
  have hpiece := sameRay_piece_total_of_norm_sum_eq s A hnorm
  intro j hj k hk
  by_cases htot : (∑ i ∈ s, A i) = 0
  · -- total zero ⟹ all norms zero ⟹ both pieces zero
    have hsum0 : ∑ i ∈ s, ‖A i‖ = 0 := by rw [← hnorm, htot, norm_zero]
    have hAj0 : A j = 0 :=
      norm_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => norm_nonneg _)).mp hsum0 j hj)
    rw [hAj0]; exact SameRay.zero_left _
  · -- both same-ray with nonzero total ⟹ same-ray with each other
    exact SameRay.trans (hpiece j hj) ((hpiece k hk).symm) (fun h => absurd h htot)

/-- Norm-additivity (`‖∑ A i‖ = ∑ ‖A i‖`) is EQUIVALENT to multi-piece coherence saturation
`ρ = 1`, given a positive total piece-mass denominator. -/
theorem multiPieceNormCoherence_eq_one_iff_norm_sum_eq {ι : Type*} (s : Finset ι) (A : ι → E)
    (hden : 0 < ∑ i ∈ s, ‖A i‖) :
    multiPieceNormCoherence s A = 1 ↔ ‖∑ i ∈ s, A i‖ = ∑ i ∈ s, ‖A i‖ := by
  unfold multiPieceNormCoherence
  rw [div_eq_one_iff_eq (ne_of_gt hden)]

/-- A piece is same-ray with a finite sum of pieces, provided it is same-ray with every summand.
This is the reverse-direction engine: `SameRay` to each summand lifts to `SameRay` to their sum,
by `Finset` induction off `SameRay.add_right`. -/
theorem sameRay_sum_of_forall_sameRay {ι : Type*} (v : E) (s : Finset ι) (A : ι → E)
    (h : ∀ i ∈ s, SameRay ℝ v (A i)) :
    SameRay ℝ v (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (SameRay.zero_right v)
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    have ha' : SameRay ℝ v (A a) := h a (Finset.mem_insert_self a t)
    have ht' : ∀ i ∈ t, SameRay ℝ v (A i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact SameRay.add_right ha' (ih ht')

/-- Pairwise same-ray pieces have norm-additive sum (`‖∑ A i‖ = ∑ ‖A i‖`).  This is the
full-generality reverse direction, recovering `_DoorIVComplexRayCoherence`'s common-ray forward
fact without assuming a presented common vector. -/
theorem norm_sum_eq_of_pairwise_sameRay {ι : Type*} (s : Finset ι) (A : ι → E)
    (hpair : ∀ j ∈ s, ∀ k ∈ s, SameRay ℝ (A j) (A k)) :
    ‖∑ i ∈ s, A i‖ = ∑ i ∈ s, ‖A i‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    have hpair_t : ∀ j ∈ t, ∀ k ∈ t, SameRay ℝ (A j) (A k) := fun j hj k hk =>
      hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    have htsum : ‖∑ i ∈ t, A i‖ = ∑ i ∈ t, ‖A i‖ := ih hpair_t
    -- A a is same-ray with every piece in t, hence same-ray with ∑_t
    have ha_each : ∀ i ∈ t, SameRay ℝ (A a) (A i) := fun i hi =>
      hpair a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
    have ha_t : SameRay ℝ (A a) (∑ i ∈ t, A i) :=
      sameRay_sum_of_forall_sameRay (A a) t A ha_each
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [(sameRay_iff_norm_add).mp ha_t, htsum]

/-- **The sharp multi-piece coherence saturation criterion (the new theorem).** In a strictly convex
space, multi-piece coherence equals `1` if and only if the pieces are pairwise same-ray.  The forward
direction is the multi-piece converse proved here; the reverse direction recovers the
`_DoorIVComplexRayCoherence` forward fact at full generality (pairwise same-ray ⟹ saturation). -/
theorem multiPieceNormCoherence_eq_one_iff_pairwise_sameRay {ι : Type*} (s : Finset ι) (A : ι → E)
    (hden : 0 < ∑ i ∈ s, ‖A i‖) :
    multiPieceNormCoherence s A = 1 ↔ (∀ j ∈ s, ∀ k ∈ s, SameRay ℝ (A j) (A k)) := by
  rw [multiPieceNormCoherence_eq_one_iff_norm_sum_eq s A hden]
  exact ⟨pairwise_sameRay_of_norm_sum_eq s A, norm_sum_eq_of_pairwise_sameRay s A⟩

/-- **Strict door-(iv) obstruction (multi-piece, sharp form).** A strict multi-piece coherence drop
`ρ < 1` is EQUIVALENT to the existence of a genuinely non-collinear pair among the pieces.  Thus any
multi-piece refinement claiming a strict saving must exhibit a non-same-ray pair; subdivision alone
contributes nothing. -/
theorem multiPieceNormCoherence_lt_one_iff_exists_not_sameRay {ι : Type*} (s : Finset ι) (A : ι → E)
    (hden : 0 < ∑ i ∈ s, ‖A i‖) :
    multiPieceNormCoherence s A < 1 ↔ (∃ j ∈ s, ∃ k ∈ s, ¬ SameRay ℝ (A j) (A k)) := by
  have hle : multiPieceNormCoherence s A ≤ 1 := by
    unfold multiPieceNormCoherence
    have htri : ‖∑ i ∈ s, A i‖ ≤ ∑ i ∈ s, ‖A i‖ := norm_sum_le _ _
    rw [div_le_one hden]; exact htri
  rw [lt_iff_le_and_ne, and_iff_right hle]
  rw [ne_eq, multiPieceNormCoherence_eq_one_iff_pairwise_sameRay s A hden]
  push_neg
  rfl

end ProximityGap.Frontier.DoorIVMultiPieceSameRayConverse

#print axioms ProximityGap.Frontier.DoorIVMultiPieceSameRayConverse.sameRay_piece_total_of_norm_sum_eq
#print axioms ProximityGap.Frontier.DoorIVMultiPieceSameRayConverse.pairwise_sameRay_of_norm_sum_eq
#print axioms ProximityGap.Frontier.DoorIVMultiPieceSameRayConverse.sameRay_sum_of_forall_sameRay
#print axioms ProximityGap.Frontier.DoorIVMultiPieceSameRayConverse.norm_sum_eq_of_pairwise_sameRay
#print axioms ProximityGap.Frontier.DoorIVMultiPieceSameRayConverse.multiPieceNormCoherence_eq_one_iff_norm_sum_eq
#print axioms ProximityGap.Frontier.DoorIVMultiPieceSameRayConverse.multiPieceNormCoherence_eq_one_iff_pairwise_sameRay
#print axioms ProximityGap.Frontier.DoorIVMultiPieceSameRayConverse.multiPieceNormCoherence_lt_one_iff_exists_not_sameRay
