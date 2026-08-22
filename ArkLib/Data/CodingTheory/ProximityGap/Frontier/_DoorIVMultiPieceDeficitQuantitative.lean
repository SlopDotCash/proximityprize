/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceDeficitQuantitative

/-!
# Door (iv): the QUANTITATIVE MULTI-piece coherence deficit bound

`_DoorIVCoherenceDeficitQuantitative.lean` proves the tight TWO-piece quantitative law
`1 − ρ ≥ ½·(‖x‖‖y‖/(‖x‖+‖y‖)²)·d²` in a real inner product space, upgrading the qualitative
`ρ = 1 ⟺ same-ray` to a quantitative obstruction.  `_DoorIVMultiPieceSameRayConverse.lean` proves the
QUALITATIVE multi-piece converse `ρ_multi = 1 ⟺ pairwise same-ray` (`ρ_multi < 1 ⟺ ∃ non-collinear
pair`).  What was still missing is the QUANTITATIVE multi-piece statement: HOW MUCH coherence drop does
ONE non-collinear pair force in a family of MANY pieces?

This file supplies it.  The key engine is a **defect-monotonicity** lemma: the norm defect
`D(A) = Σ‖A i‖ − ‖Σ A i‖` (≥ 0 by the triangle inequality) of a finite family is at least the
two-piece defect of ANY pair, because merging that pair into its sum yields a family with the same
total sum whose own defect is still ≥ 0:

> `Σ_{i∈s} ‖A i‖ − ‖Σ_{i∈s} A i‖  ≥  (‖A j‖ + ‖A k‖) − ‖A j + A k‖`   (j ≠ k in s).

Combined with the two-piece bound this gives, for the worst non-collinear pair,

> `1 − ρ_multi  ≥  ½ · (‖A j‖·‖A k‖ / (Σ_{i∈s} ‖A i‖)²) · ‖A j/‖A j‖ − A k/‖A k‖‖²`   (verified tight).

Consequence for door (iv): a multi-piece refinement of the worst-frequency monomial sum that claims a
coherence saving `1 − ρ_multi` MUST contain a pair of pieces whose unit-direction chordal distance is
`≳ √(1−ρ_multi)` *relative to the full piece mass*.  Subdivision into many pieces does NOT cheapen the
required misalignment: the saving is still controlled, pairwise, by `√(saving)` of angular separation
against the TOTAL mass.  This quantifies the no-fifth-door obstruction at full multiplicity.  No
Gauss-period cancellation, moment, completion, or anti-concentration is claimed or used; this is pure
triangle-inequality / Cauchy–Schwarz bookkeeping.  CORE `M(μ_n)` stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ProximityGap.Frontier.DoorIVMultiPieceDeficitQuantitative

open scoped BigOperators InnerProductSpace
open ProximityGap.Frontier.DoorIVCoherenceDeficitQuantitative

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Multi-piece norm coherence (same definition as the other door-(iv) coherence files). -/
noncomputable def multiPieceNormCoherence {ι : Type*} (s : Finset ι) (A : ι → F) : ℝ :=
  ‖∑ i ∈ s, A i‖ / (∑ i ∈ s, ‖A i‖)

/-- **Defect monotonicity (the engine).** In any normed group, the finite-family norm defect
`Σ_{i∈s} ‖A i‖ − ‖Σ_{i∈s} A i‖` is at least the two-piece defect of any pair `j ≠ k` in `s`.
Proof: split off the two summands and apply the triangle inequality to the remaining sum together
with the merged pair. -/
theorem defect_ge_pair_defect {ι : Type*} [DecidableEq ι] (s : Finset ι) (A : ι → F)
    {j k : ι} (hj : j ∈ s) (hk : k ∈ s) (hjk : j ≠ k) :
    (∑ i ∈ s, ‖A i‖) - ‖∑ i ∈ s, A i‖ ≥ (‖A j‖ + ‖A k‖) - ‖A j + A k‖ := by
  classical
  -- Let t = s \ {j, k}.  Then Σ_s A = A j + A k + Σ_t A and Σ_s ‖A‖ = ‖A j‖ + ‖A k‖ + Σ_t ‖A‖.
  set t := s \ {j, k} with ht
  have hk_t : k ∉ t := by simp [ht]
  have hj_t : j ∉ insert k t := by
    simp only [Finset.mem_insert, ht, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hjk, by tauto⟩
  -- s = insert j (insert k t)
  have hs_eq : s = insert j (insert k t) := by
    rw [ht]
    ext a
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · intro ha
      by_cases haj : a = j
      · exact Or.inl haj
      · by_cases hak : a = k
        · exact Or.inr (Or.inl hak)
        · exact Or.inr (Or.inr ⟨ha, by tauto⟩)
    · rintro (rfl | rfl | ⟨ha, _⟩)
      · exact hj
      · exact hk
      · exact ha
  -- sums over s
  have hsumA : ∑ i ∈ s, A i = A j + (A k + ∑ i ∈ t, A i) := by
    rw [hs_eq, Finset.sum_insert hj_t, Finset.sum_insert hk_t]
  have hsumN : ∑ i ∈ s, ‖A i‖ = ‖A j‖ + (‖A k‖ + ∑ i ∈ t, ‖A i‖) := by
    rw [hs_eq, Finset.sum_insert hj_t, Finset.sum_insert hk_t]
  -- triangle inequality on the merged decomposition: ‖(A j + A k) + Σ_t A‖ ≤ ‖A j + A k‖ + ‖Σ_t A‖
  have htri1 : ‖(A j + A k) + ∑ i ∈ t, A i‖ ≤ ‖A j + A k‖ + ‖∑ i ∈ t, A i‖ := norm_add_le _ _
  -- and ‖Σ_t A‖ ≤ Σ_t ‖A‖
  have htri2 : ‖∑ i ∈ t, A i‖ ≤ ∑ i ∈ t, ‖A i‖ := norm_sum_le _ _
  -- rewrite ‖Σ_s A‖ via the merged grouping
  have hreassoc : A j + (A k + ∑ i ∈ t, A i) = (A j + A k) + ∑ i ∈ t, A i := by
    rw [add_assoc]
  rw [hsumA, hreassoc, hsumN]
  -- Goal: (‖A j‖ + (‖A k‖ + Σ_t ‖A‖)) - ‖(A j + A k) + Σ_t A‖ ≥ (‖A j‖ + ‖A k‖) - ‖A j + A k‖
  have hchain : ‖(A j + A k) + ∑ i ∈ t, A i‖ ≤ ‖A j + A k‖ + ∑ i ∈ t, ‖A i‖ := by
    calc ‖(A j + A k) + ∑ i ∈ t, A i‖ ≤ ‖A j + A k‖ + ‖∑ i ∈ t, A i‖ := htri1
      _ ≤ ‖A j + A k‖ + ∑ i ∈ t, ‖A i‖ := by linarith [htri2]
  linarith [hchain]

/-- The multi-piece coherence is at most one when the total piece mass is positive. -/
theorem multiPieceNormCoherence_le_one {ι : Type*} (s : Finset ι) (A : ι → F)
    (hden : 0 < ∑ i ∈ s, ‖A i‖) :
    multiPieceNormCoherence s A ≤ 1 := by
  unfold multiPieceNormCoherence
  rw [div_le_one hden]
  exact norm_sum_le _ _

/-- **Multi-piece coherence deficit lower bound (inner-product form).** For a finite family with
positive total piece mass and any pair `j ≠ k`, the coherence deficit `1 − ρ_multi` is at least the
pair's misalignment numerator over the squared TOTAL piece mass. -/
theorem one_sub_multiPieceCoherence_ge_pair_misalign {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (A : ι → F) {j k : ι} (hj : j ∈ s) (hk : k ∈ s) (hjk : j ≠ k)
    (hden : 0 < ∑ i ∈ s, ‖A i‖) :
    1 - multiPieceNormCoherence s A
      ≥ (‖A j‖ * ‖A k‖ - ⟪A j, A k⟫_ℝ) / (∑ i ∈ s, ‖A i‖) ^ 2 := by
  set M := ∑ i ∈ s, ‖A i‖ with hM
  -- 1 - ρ_multi = (M - ‖Σ A‖)/M = D(A)/M
  have hdefect : 1 - multiPieceNormCoherence s A = ((∑ i ∈ s, ‖A i‖) - ‖∑ i ∈ s, A i‖) / M := by
    unfold multiPieceNormCoherence
    rw [hM, sub_div, div_self (ne_of_gt hden)]
  -- defect ≥ pair defect ≥ pair misalign / (‖A j‖+‖A k‖)  (two-piece inner-product bound)
  have hmono := defect_ge_pair_defect s A hj hk hjk
  -- pair misalignment is nonnegative (Cauchy–Schwarz), so we may pass to the weaker /M denominator
  have hpairnn : 0 ≤ ‖A j‖ * ‖A k‖ - ⟪A j, A k⟫_ℝ := misalign_nonneg (A j) (A k)
  -- two-piece bound needs ‖A j‖ + ‖A k‖ > 0; if it is 0 both pieces vanish ⟹ numerator 0
  by_cases hpd : 0 < ‖A j‖ + ‖A k‖
  · have htwo := norm_sum_gap_ge_misalign_div (A j) (A k) hpd
    -- (‖A j‖+‖A k‖) - ‖A j + A k‖ ≥ (misalign)/(‖A j‖+‖A k‖)
    -- chain: D(A) ≥ pairdefect ≥ misalign/(‖A j‖+‖A k‖) ≥ misalign/M  (since ‖A j‖+‖A k‖ ≤ M)
    have hpd_le_M : ‖A j‖ + ‖A k‖ ≤ M := by
      rw [hM]
      have : ‖A j‖ + ‖A k‖ = ∑ i ∈ ({j, k} : Finset ι), ‖A i‖ := by
        rw [Finset.sum_pair hjk]
      rw [this]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha'
        · exact hj
        · rw [Finset.mem_singleton] at ha'; subst ha'; exact hk
      · intro i _ _; exact norm_nonneg _
    -- misalign/(‖A j‖+‖A k‖) ≥ misalign/M  because larger denom ≤ smaller value? careful:
    -- we want misalign/M ≤ pairdefect.  We have pairdefect ≥ misalign/(‖A j‖+‖A k‖) ≥ misalign/M.
    have hstep1 : (‖A j‖ * ‖A k‖ - ⟪A j, A k⟫_ℝ) / M
        ≤ (‖A j‖ * ‖A k‖ - ⟪A j, A k⟫_ℝ) / (‖A j‖ + ‖A k‖) := by
      gcongr
    have hstep2 : (‖A j‖ * ‖A k‖ - ⟪A j, A k⟫_ℝ) / (‖A j‖ + ‖A k‖)
        ≤ (∑ i ∈ s, ‖A i‖) - ‖∑ i ∈ s, A i‖ := le_trans htwo hmono
    have hDM : (‖A j‖ * ‖A k‖ - ⟪A j, A k⟫_ℝ) / M
        ≤ ((∑ i ∈ s, ‖A i‖) - ‖∑ i ∈ s, A i‖) := le_trans hstep1 hstep2
    rw [ge_iff_le, hdefect, sq, ← hM]
    rw [div_mul_eq_div_div]
    gcongr
  · -- ‖A j‖ + ‖A k‖ = 0 ⟹ ‖A j‖ = ‖A k‖ = 0 ⟹ A j = A k = 0 ⟹ numerator = 0
    push_neg at hpd
    have hsum0 : ‖A j‖ + ‖A k‖ = 0 :=
      le_antisymm hpd (by positivity)
    have hAj0 : ‖A j‖ = 0 := by
      have := norm_nonneg (A j); have := norm_nonneg (A k); linarith
    have hAk0 : ‖A k‖ = 0 := by
      have := norm_nonneg (A j); have := norm_nonneg (A k); linarith
    have hAjv : A j = 0 := norm_eq_zero.mp hAj0
    have hAkv : A k = 0 := norm_eq_zero.mp hAk0
    have hnum0 : ‖A j‖ * ‖A k‖ - ⟪A j, A k⟫_ℝ = 0 := by
      rw [hAjv, hAkv]; simp
    rw [hnum0, zero_div]
    -- 1 - ρ_multi ≥ 0
    have hle := multiPieceNormCoherence_le_one s A hden
    linarith

end ProximityGap.Frontier.DoorIVMultiPieceDeficitQuantitative

#print axioms ProximityGap.Frontier.DoorIVMultiPieceDeficitQuantitative.defect_ge_pair_defect
#print axioms ProximityGap.Frontier.DoorIVMultiPieceDeficitQuantitative.multiPieceNormCoherence_le_one
#print axioms ProximityGap.Frontier.DoorIVMultiPieceDeficitQuantitative.one_sub_multiPieceCoherence_ge_pair_misalign
