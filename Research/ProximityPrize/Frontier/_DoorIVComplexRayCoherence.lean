/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Convex.StrictConvexSpace

/-!
# Door (iv): complex/two-vector coherence is exactly same-ray saturation

The half-coset and real-piece Door-IV files show that negation-stable refinements collapse to a
real sign-mass problem.  This file records the corresponding phase-sensitive constraint for any
strictly convex real normed space, in particular `ℂ`: a two-piece split has coherence one exactly
when the two vector pieces lie on the same nonnegative ray.  Therefore a genuine two-piece phase
anti-concentration theorem cannot merely subdivide the sum; it must prove non-collinearity (or
quantitative distance from same-ray alignment) for the adversarial pieces.

No Gauss-period cancellation is claimed here.  These are pure triangle-equality bookkeeping lemmas
for the localized Door-IV coherence object.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ProximityGap.Frontier.DoorIVComplexRayCoherence

variable {E : Type*} [NormedAddCommGroup E]

/-- Two-piece norm coherence: the ratio between the norm of the combined vector and the sum of
piece norms.  For complex Gauss-period pieces this is the phase-alignment ratio of the split. -/
noncomputable def twoPieceNormCoherence (x y : E) : ℝ :=
  ‖x + y‖ / (‖x‖ + ‖y‖)

/-- The two-piece coherence is always at most one when the denominator is positive. -/
theorem twoPieceNormCoherence_le_one {x y : E} (hden : 0 < ‖x‖ + ‖y‖) :
    twoPieceNormCoherence x y ≤ 1 := by
  unfold twoPieceNormCoherence
  have htri : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have hdiv : ‖x + y‖ / (‖x‖ + ‖y‖) ≤ (‖x‖ + ‖y‖) / (‖x‖ + ‖y‖) :=
    div_le_div_of_nonneg_right htri (le_of_lt hden)
  simpa [div_self (ne_of_gt hden)] using hdiv

/-! ## Finite-refinement same-ray obstruction

The same triangle-equality obstruction persists for any finite refinement: if every vector piece is a
nonnegative scalar multiple of one common vector, then the normalized multi-piece coherence is exactly
`1`.  Thus a strict multi-piece phase-saving theorem must prove that the adversarial pieces are not all
carried by a common nonnegative ray.
-/

/-- Normalized norm coherence of finitely many vector pieces. -/
noncomputable def multiPieceNormCoherence {ι : Type*} (s : Finset ι) (A : ι → E) : ℝ :=
  ‖∑ i ∈ s, A i‖ / (∑ i ∈ s, ‖A i‖)

/-- Multi-piece norm coherence is always at most one when the denominator is positive.  This
is the finite-refinement triangle-inequality ceiling; all nontrivial Door-IV work is in proving
strict slack away from this ceiling at the adversarial frequency. -/
theorem multiPieceNormCoherence_le_one {ι : Type*} (s : Finset ι) (A : ι → E)
    (hden : 0 < ∑ i ∈ s, ‖A i‖) :
    multiPieceNormCoherence s A ≤ 1 := by
  unfold multiPieceNormCoherence
  have htri : ‖∑ i ∈ s, A i‖ ≤ ∑ i ∈ s, ‖A i‖ := norm_sum_le _ _
  have hdiv : ‖∑ i ∈ s, A i‖ / (∑ i ∈ s, ‖A i‖)
      ≤ (∑ i ∈ s, ‖A i‖) / (∑ i ∈ s, ‖A i‖) :=
    div_le_div_of_nonneg_right htri (le_of_lt hden)
  simpa [div_self (ne_of_gt hden)] using hdiv

variable [NormedSpace ℝ E]

/-- If every piece lies on the same nonnegative ray `ℝ_{≥0} • u` and the scalar mass is
positive, then multi-piece norm coherence is exactly `1`.  Subdivision alone supplies no phase
cancellation while the pieces remain collinear on one nonnegative ray. -/
theorem multiPieceNormCoherence_eq_one_of_common_nonneg_ray {ι : Type*}
    (s : Finset ι) (A : ι → E) (u : E) (c : ι → ℝ)
    (hA : ∀ i ∈ s, A i = c i • u)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (hsum_pos : 0 < ∑ i ∈ s, c i) (hu : u ≠ 0) :
    multiPieceNormCoherence s A = 1 := by
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, c i := le_of_lt hsum_pos
  have hnormu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hsumA : (∑ i ∈ s, A i) = (∑ i ∈ s, c i) • u := by
    calc
      (∑ i ∈ s, A i) = ∑ i ∈ s, c i • u := by
        exact Finset.sum_congr rfl (fun i hi => hA i hi)
      _ = (∑ i ∈ s, c i) • u := by
        rw [Finset.sum_smul]
  have hnum : ‖∑ i ∈ s, A i‖ = (∑ i ∈ s, c i) * ‖u‖ := by
    rw [hsumA, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
  have hden : (∑ i ∈ s, ‖A i‖) = (∑ i ∈ s, c i) * ‖u‖ := by
    calc
      (∑ i ∈ s, ‖A i‖) = ∑ i ∈ s, c i * ‖u‖ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hA i hi, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc i hi)]
      _ = (∑ i ∈ s, c i) * ‖u‖ := by
        rw [Finset.sum_mul]
  have hprod_ne : (∑ i ∈ s, c i) * ‖u‖ ≠ 0 := ne_of_gt (mul_pos hsum_pos hnormu_pos)
  unfold multiPieceNormCoherence
  rw [hnum, hden, div_self hprod_ne]

/-- Threshold obstruction: any multi-piece coherence theorem proving a strict bound below `1` must
rule out common nonnegative-ray alignment of all pieces. -/
theorem not_common_nonneg_ray_of_multiPieceNormCoherence_le {ι : Type*}
    (s : Finset ι) (A : ι → E) {θ : ℝ}
    (hθ : θ < 1) (hcoh : multiPieceNormCoherence s A ≤ θ) :
    ¬ ∃ (u : E) (c : ι → ℝ),
      (∀ i ∈ s, A i = c i • u) ∧
      (∀ i ∈ s, 0 ≤ c i) ∧
      0 < (∑ i ∈ s, c i) ∧ u ≠ 0 := by
  rintro ⟨u, c, hA, hc, hsum_pos, hu⟩
  have hone : multiPieceNormCoherence s A = 1 :=
    multiPieceNormCoherence_eq_one_of_common_nonneg_ray s A u c hA hc hsum_pos hu
  linarith

/-- Epsilon-drop form: a positive `1 - ε` saving is impossible while all pieces may lie on one
common nonnegative ray. -/
theorem common_nonneg_ray_not_multiPieceNormCoherence_le_one_sub {ι : Type*}
    (s : Finset ι) (A : ι → E) {ε : ℝ}
    (hε : 0 < ε)
    (hray : ∃ (u : E) (c : ι → ℝ),
      (∀ i ∈ s, A i = c i • u) ∧
      (∀ i ∈ s, 0 ≤ c i) ∧
      0 < (∑ i ∈ s, c i) ∧ u ≠ 0) :
    ¬ multiPieceNormCoherence s A ≤ 1 - ε := by
  intro hcoh
  exact not_common_nonneg_ray_of_multiPieceNormCoherence_le s A (sub_lt_self 1 hε) hcoh hray

/-- Family audit form: a universal positive epsilon-drop for finite refinements forces every
indexed split to exclude common nonnegative-ray alignment.  This is the forward constraint interface
for Door-IV certificates: the claimed strict coherence saving carries a member-by-member geometric
obligation before any arithmetic anti-concentration can be used. -/
theorem forall_not_common_nonneg_ray_of_family_multiPieceNormCoherence_le_one_sub
    {κ ι : Type*} (s : κ → Finset ι) (A : κ → ι → E) {ε : κ → ℝ}
    (hε : ∀ k, 0 < ε k)
    (hcoh : ∀ k, multiPieceNormCoherence (s k) (A k) ≤ 1 - ε k) :
    ∀ k, ¬ ∃ (u : E) (c : ι → ℝ),
      (∀ i ∈ s k, A k i = c i • u) ∧
      (∀ i ∈ s k, 0 ≤ c i) ∧
      0 < (∑ i ∈ s k, c i) ∧ u ≠ 0 := by
  intro k hk
  exact common_nonneg_ray_not_multiPieceNormCoherence_le_one_sub (s k) (A k) (hε k) hk (hcoh k)

/-- Family multi-piece ray obstruction: a universal positive epsilon-drop for finite refinements must
exclude common nonnegative-ray alignment at every indexed split.  One aligned member, even after further
subdivision into many pieces, refutes the whole strict-coherence family. -/
theorem not_family_multiPieceNormCoherence_le_one_sub_of_exists_common_nonneg_ray
    {κ ι : Type*} (s : κ → Finset ι) (A : κ → ι → E) {ε : κ → ℝ}
    (hε : ∀ k, 0 < ε k)
    (hbad : ∃ k, ∃ (u : E) (c : ι → ℝ),
      (∀ i ∈ s k, A k i = c i • u) ∧
      (∀ i ∈ s k, 0 ≤ c i) ∧
      0 < (∑ i ∈ s k, c i) ∧ u ≠ 0) :
    ¬ ∀ k, multiPieceNormCoherence (s k) (A k) ≤ 1 - ε k := by
  intro hcoh
  rcases hbad with ⟨k, hk⟩
  exact (forall_not_common_nonneg_ray_of_family_multiPieceNormCoherence_le_one_sub s A hε hcoh k) hk

variable [StrictConvexSpace ℝ E]

/-- Saturation of two-piece norm coherence is exactly triangle-equality saturation, hence the two
pieces lie on the same nonnegative ray.  This is the complex/phase analogue of the real same-sign
lemmas: a claimed `ρ = 1` alignment is precisely a same-ray statement, not a new cancellation bound. -/
theorem twoPieceNormCoherence_eq_one_iff_sameRay {x y : E} (hden : 0 < ‖x‖ + ‖y‖) :
    twoPieceNormCoherence x y = 1 ↔ SameRay ℝ x y := by
  constructor
  · intro h
    have hnorm : ‖x + y‖ = ‖x‖ + ‖y‖ := by
      have hmul := congrArg (fun t : ℝ => t * (‖x‖ + ‖y‖)) h
      unfold twoPieceNormCoherence at hmul
      simpa [div_mul_cancel₀ _ (ne_of_gt hden)] using hmul
    exact (sameRay_iff_norm_add (x := x) (y := y)).2 hnorm
  · intro h
    unfold twoPieceNormCoherence
    have hnorm : ‖x + y‖ = ‖x‖ + ‖y‖ :=
      (sameRay_iff_norm_add (x := x) (y := y)).1 h
    rw [hnorm, div_self (ne_of_gt hden)]

/-- Contrapositive form: any non-same-ray two-piece split has strict coherence slack.  Thus a
useful Door-IV two-piece anti-concentration lemma must prove genuine phase non-collinearity for the
pieces; without that, triangle equality allows `ρ = 1`. -/
theorem twoPieceNormCoherence_lt_one_of_not_sameRay {x y : E} (hden : 0 < ‖x‖ + ‖y‖)
    (h : ¬ SameRay ℝ x y) :
    twoPieceNormCoherence x y < 1 := by
  unfold twoPieceNormCoherence
  have hlt : ‖x + y‖ < ‖x‖ + ‖y‖ :=
    (not_sameRay_iff_norm_add_lt (x := x) (y := y)).1 h
  have hdiv : ‖x + y‖ / (‖x‖ + ‖y‖) < (‖x‖ + ‖y‖) / (‖x‖ + ‖y‖) :=
    div_lt_div_of_pos_right hlt hden
  simpa [div_self (ne_of_gt hden)] using hdiv

/-- Exact strict-slack criterion for a two-piece split: coherence drops below `1` if and only if
the pieces are not on the same nonnegative ray.  This packages the Door-IV obstruction in the
probe-facing form: a two-piece refinement has no hidden slack unless it proves non-same-ray phase
geometry at the adversarial frequency. -/
theorem twoPieceNormCoherence_lt_one_iff_not_sameRay {x y : E} (hden : 0 < ‖x‖ + ‖y‖) :
    twoPieceNormCoherence x y < 1 ↔ ¬ SameRay ℝ x y := by
  constructor
  · intro hlt hsame
    have hone : twoPieceNormCoherence x y = 1 :=
      (twoPieceNormCoherence_eq_one_iff_sameRay (x := x) (y := y) hden).2 hsame
    linarith
  · intro h
    exact twoPieceNormCoherence_lt_one_of_not_sameRay (x := x) (y := y) hden h

/-- Threshold obstruction: any claimed two-piece coherence drop below a fixed `θ < 1` must first
rule out same-ray alignment of the pieces. -/
theorem not_sameRay_of_twoPieceNormCoherence_le {x y : E} {θ : ℝ} (hden : 0 < ‖x‖ + ‖y‖)
    (hθ : θ < 1) (hcoh : twoPieceNormCoherence x y ≤ θ) :
    ¬ SameRay ℝ x y := by
  intro hsame
  have hone : twoPieceNormCoherence x y = 1 :=
    (twoPieceNormCoherence_eq_one_iff_sameRay (x := x) (y := y) hden).2 hsame
  linarith

/-- Epsilon-drop obstruction: same-ray alignment forbids any positive `1 - ε` coherence bound. -/
theorem sameRay_not_twoPieceNormCoherence_le_one_sub {x y : E} {ε : ℝ}
    (hden : 0 < ‖x‖ + ‖y‖) (hε : 0 < ε) (hsame : SameRay ℝ x y) :
    ¬ twoPieceNormCoherence x y ≤ 1 - ε := by
  intro hcoh
  exact (not_sameRay_of_twoPieceNormCoherence_le (x := x) (y := y) (θ := 1 - ε) hden
    (sub_lt_self 1 hε) hcoh) hsame

/-- Family audit form: a universal positive coherence drop below `1` for two-piece Door-IV
splits forces non-same-ray geometry at every indexed member. -/
theorem forall_not_sameRay_of_family_twoPieceNormCoherence_le_one_sub {ι : Type*}
    (x y : ι → E) {ε : ι → ℝ}
    (hden : ∀ i, 0 < ‖x i‖ + ‖y i‖) (hε : ∀ i, 0 < ε i)
    (hcoh : ∀ i, twoPieceNormCoherence (x i) (y i) ≤ 1 - ε i) :
    ∀ i, ¬ SameRay ℝ (x i) (y i) := by
  intro i hi
  exact sameRay_not_twoPieceNormCoherence_le_one_sub (hden i) (hε i) hi (hcoh i)

/-- Family epsilon-drop obstruction: a universal positive coherence drop below `1` for two-piece
Door-IV splits must rule out same-ray alignment at every indexed member.  One same-ray member with
positive denominator refutes the whole family of strict `1 - ε_i` caps. -/
theorem not_family_twoPieceNormCoherence_le_one_sub_of_exists_sameRay {ι : Type*}
    (x y : ι → E) {ε : ι → ℝ}
    (hden : ∀ i, 0 < ‖x i‖ + ‖y i‖) (hε : ∀ i, 0 < ε i)
    (hbad : ∃ i, SameRay ℝ (x i) (y i)) :
    ¬ ∀ i, twoPieceNormCoherence (x i) (y i) ≤ 1 - ε i := by
  intro hcoh
  rcases hbad with ⟨i, hi⟩
  exact (forall_not_sameRay_of_family_twoPieceNormCoherence_le_one_sub x y hden hε hcoh i) hi

end ProximityGap.Frontier.DoorIVComplexRayCoherence

#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence_le_one
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence_eq_one_iff_sameRay
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence_lt_one_of_not_sameRay
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence_lt_one_iff_not_sameRay
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.not_sameRay_of_twoPieceNormCoherence_le
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.sameRay_not_twoPieceNormCoherence_le_one_sub
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.forall_not_sameRay_of_family_twoPieceNormCoherence_le_one_sub
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.not_family_twoPieceNormCoherence_le_one_sub_of_exists_sameRay
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.multiPieceNormCoherence_le_one
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.multiPieceNormCoherence_eq_one_of_common_nonneg_ray
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.not_common_nonneg_ray_of_multiPieceNormCoherence_le
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.common_nonneg_ray_not_multiPieceNormCoherence_le_one_sub
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.forall_not_common_nonneg_ray_of_family_multiPieceNormCoherence_le_one_sub
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.not_family_multiPieceNormCoherence_le_one_sub_of_exists_common_nonneg_ray
