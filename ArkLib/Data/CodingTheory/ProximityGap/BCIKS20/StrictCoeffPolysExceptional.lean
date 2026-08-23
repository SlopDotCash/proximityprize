/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves

/-!
# BCIKS20 §5/§6 — exceptional-set form of the strict coefficient-polynomial residual

`StrictCoeffPolysResidual` (`Curves.lean`) demands that every decoded family `P` over the
good-coefficient set `RS_goodCoeffsCurve` admits ONE coefficient family `B` (each `B j` of
degree `< k + 1`) with `(P z).coeff j = (B j).eval z` at EVERY good `z`.  Above the
unique-decoding radius `(1 - ρ)/2 < δ` — which the residual's own Johnson-side hypothesis
grants — this is too strong: per BCHKS25 (eprint 2025/2055, results 3–4) exceptional
parameters are provably necessary in the Johnson regime, and BCIKS20's own §5 conclusion
only pins the decoded family to the curve coefficients away from an `O(n)`-size exceptional
set of `z`'s.

This file builds the honest **exceptional-set residual** and its consumer chain:

* `StrictCoeffPolysExcResidual b` — verbatim `StrictCoeffPolysResidual`, except the
  conclusion allows an exceptional set `E` with `E.card ≤ b`: the coefficient-polynomial
  identity is only required at good `z ∉ E`.
* `strictCoeffPolysExcResidual_of_strictCoeffPolysResidual` /
  `strictCoeffPolysResidual_of_strictCoeffPolysExcResidual_zero` — the `b = 0` case is
  exactly the original residual, so the new surface is a strict weakening for `b > 0`.
* `subset_single_decoded_family_coeff_polys_implies_jointAgreement_core` (and its
  positive-`k` wrapper) — single-family forms of the in-tree subset counting core
  `subset_goodCoeffsCurve_coeff_polys_implies_jointAgreement_core`.  The in-tree core is
  already stated at an abstract subset `S' ⊆ RS_goodCoeffsCurve`, but its
  `∀ P`-quantified extraction interface cannot be fed from the exceptional residual: the
  exceptional set `E` (hence the surviving subset `S' = good \ E`) **depends on the decoded
  family `P`**.  The single-family forms chain the identical bricks
  (`decoded_family_coefficients_of_coeff_polys_core`,
  `decoded_family_coefficients_assemble_codeword_curve`,
  `decoded_sum_polynomial_family_on_codeword_curve_implies_jointAgreement`), none of which
  uses goodness of any parameter outside `S'`.
* `RS_jointAgreement_of_prob_gt_exc` — the §6 consumer: a probability threshold `η` whose
  mass absorbs the exceptional budget (`k·errorBound·|F| + b ≤ η·|F|`, the named card
  inequality) still yields `jointAgreement`, by running the counting argument on
  `RS_goodCoeffsCurve \ E`.
* `RS_jointAgreement_of_prob_gt_strict_johnson_exc` — the strict-Johnson instantiation at
  the explicit threshold `k · (errorBound + b/|F|)`.
* `correlatedAgreement_affine_curves_of_strict_coeff_polys_exc` — the final keystone:
  Theorem 1.5 from the exceptional-set residual, at the adjusted proximity error
  `ε = errorBound δ deg domain + b / |F|`.
* `correlatedAgreement_affine_curves_strict_of_strict_coeff_polys_exc` — the strict-interior
  front door that does not carry the documented-false boundary residual.
-/

namespace ProximityGap

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory ENNReal
open Code

section ExceptionalResidual

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Single-family form of the subset counting core: ONE decoded family `P` on a large
parameter set `S'`, together with ONE coefficient-polynomial family `B` matching `P` on
`S'`, already forces `jointAgreement`.  Unlike
`subset_goodCoeffsCurve_coeff_polys_implies_jointAgreement_core`, no membership of `S'` in
`RS_goodCoeffsCurve` and no `∀ P`-quantified extraction interface is required: the
assembly bricks below only consume the closeness facts and the identity on `S'` itself.
This is the form an exceptional-set extraction (where the surviving set depends on the
decoded family) can feed. -/
theorem subset_single_decoded_family_coeff_polys_implies_jointAgreement_core {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    {u : Fin (l + 2) → ι → F}
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (P : F → Polynomial F)
    (hdecoded : ∀ z ∈ S',
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
          (P z).eval ∘ domain) ≤ δ)
    (B : ℕ → Polynomial F)
    (hBdeg : ∀ j < deg, (B j).natDegree < l + 2)
    (hcoeff : ∀ z ∈ S', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  obtain ⟨A, hAdeg, hPcoeff⟩ :=
    decoded_family_coefficients_of_coeff_polys_core
      (l := l) (deg := deg) (S' := S') (P := P) B
      hBdeg (fun z hz => (hdecoded z hz).1) hcoeff
  obtain ⟨v, hv, hPcurve⟩ :=
    decoded_family_coefficients_assemble_codeword_curve
      (deg := deg) (domain := domain) P A hAdeg hPcoeff
  exact decoded_sum_polynomial_family_on_codeword_curve_implies_jointAgreement
    (u := u) (deg := deg) (domain := domain) (δ := δ) (v := v)
    hv hS'_card hS'_card₁ P hdecoded hPcurve

/-- Positive-`k` form of
`subset_single_decoded_family_coeff_polys_implies_jointAgreement_core`, with the
`Fin (k + 1) ↦ Fin (l + 2)` reindexing dance performed once. -/
theorem subset_single_decoded_family_coeff_polys_implies_jointAgreement_of_pos
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    {u : Fin (k + 1) → ι → F}
    {S' : Finset F}
    (hS'_card : S'.card > k)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * k)
    (P : F → Polynomial F)
    (hdecoded : ∀ z ∈ S',
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          (P z).eval ∘ domain) ≤ δ)
    (B : ℕ → Polynomial F)
    (hBdeg : ∀ j < deg, (B j).natDegree < k + 1)
    (hcoeff : ∀ z ∈ S', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  let l : ℕ := k - 1
  have hlk : l + 1 = k := by omega
  have hlen : l + 2 = k + 1 := by omega
  let u' : Fin (l + 2) → ι → F := fun i => u (finCongr hlen i)
  have hsum : ∀ z : F,
      (∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u' t) =
        ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t := by
    intro z
    simpa [u'] using
      (curve_sum_reindex_equiv_core (F := F) (ι := ι) (e := finCongr hlen) z u
        (fun t : Fin (k + 1) => (t : ℕ)))
  have hja' :
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u') := by
    refine subset_single_decoded_family_coeff_polys_implies_jointAgreement_core
      (l := l) (deg := deg) (domain := domain) (δ := δ) (u := u') (S' := S')
      (by omega) (by rw [hlk]; exact hS'_card₁) P ?_ B ?_ hcoeff
    · intro z hz
      refine ⟨(hdecoded z hz).1, ?_⟩
      rw [hsum z]
      exact (hdecoded z hz).2
    · intro j hj
      have := hBdeg j hj
      omega
  exact jointAgreement_reindex_equiv_core
    (F := F) (ι := ι) (C := ReedSolomon.code domain deg) (δ := δ)
    (W := u) (W' := u') (e := (finCongr hlen).symm)
    (by intro i x; simp [u'])
    hja'

/-- **Exceptional-set strict Johnson extraction residual.**  Verbatim
`StrictCoeffPolysResidual`, except the §5 side may discard an exceptional set `E` of at
most `b` curve parameters: the coefficient-polynomial identity is required only at good
`z ∉ E`.  This matches the actual conclusion shape of BCIKS20 §5 and the BCHKS25
exceptional-parameter phenomenon above the unique-decoding radius; `b = 0` recovers
`StrictCoeffPolysResidual` exactly. -/
def StrictCoeffPolysExcResidual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (b : ℕ) : Prop :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
    (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
    δ < 1 - ReedSolomon.sqrtRate deg domain →
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F, ∃ E : Finset F,
          E.card ≤ b ∧
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              z ∉ E → ∀ j < deg, (P z).coeff j = (B j).eval z

/-- The original (no-exception) residual implies the exceptional-set residual at every
budget, with `E = ∅`. -/
theorem strictCoeffPolysExcResidual_of_strictCoeffPolysResidual
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (b : ℕ)
    (h : StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    StrictCoeffPolysExcResidual (k := k) (deg := deg) (domain := domain) (δ := δ) b := by
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨B, hBdeg, hBid⟩ := h hk u hprob hJ hsqrt P hP
  exact ⟨B, ∅, by simp, hBdeg, fun z hz _ j hj => hBid z hz j hj⟩

/-- **Exceptional-budget monotonicity**: a larger exceptional budget is a weaker promise —
the same coefficient polynomials and the same exceptional set witness the residual at any
budget `b' ≥ b`. Lets producers discharge at their natural sharp budget while consumers
quote any convenient looser one. -/
theorem strictCoeffPolysExcResidual_mono
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} {b b' : ℕ} (hbb : b ≤ b')
    (h : StrictCoeffPolysExcResidual (k := k) (deg := deg) (domain := domain) (δ := δ) b) :
    StrictCoeffPolysExcResidual (k := k) (deg := deg) (domain := domain) (δ := δ) b' := by
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨B, E, hEcard, hBdeg, hBid⟩ := h hk u hprob hJ hsqrt P hP
  exact ⟨B, E, le_trans hEcard hbb, hBdeg, hBid⟩

/-- At budget `b = 0` the exceptional-set residual is the original residual: the
exceptional set is forced empty. -/
theorem strictCoeffPolysResidual_of_strictCoeffPolysExcResidual_zero
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (h : StrictCoeffPolysExcResidual (k := k) (deg := deg) (domain := domain) (δ := δ) 0) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨B, E, hEcard, hBdeg, hBid⟩ := h hk u hprob hJ hsqrt P hP
  have hE : E = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hEcard)
  exact ⟨B, hBdeg, fun z hz j hj => hBid z hz (by simp [hE]) j hj⟩

/-- Cardinality bounds on the good-coefficient set from a probability threshold whose mass
absorbs the exceptional budget `b`: if `k·errorBound·|F| + b ≤ η·|F|` and the closeness
probability exceeds `η`, then the good set beats both counting thresholds **with `b` to
spare**. -/
lemma goodCoeffsCurve_card_bounds_of_prob_gt_exc {k deg : ℕ}
    {domain : ι ↪ F} {δ η : ℝ≥0} (b : ℕ) (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] > (η : ENNReal))
    (hη :
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal) + (b : ENNReal) ≤
        (η : ENNReal) * (Fintype.card F : ENNReal))
    (hsmall :
      (k : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal))
    (hlarge :
      ((((Fintype.card ι + 1) * k : ℕ) - 1 : ℕ) : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal)) :
    (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k + b ∧
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k + b := by
  classical
  have hxη :
      (η : ENNReal) * (Fintype.card F : ENNReal) <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal) :=
    goodCoeffsCurve_threshold_mul_card_lt_card_of_prob_gt
      (k := k) (deg := deg) (domain := domain) (δ := δ) (η := η) u hprob
  have hx :
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal) + (b : ENNReal) <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal) :=
    lt_of_le_of_lt hη hxη
  constructor
  · have h1 :
        ((k + b : ℕ) : ENNReal) <
          ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
            ENNReal) := by
      refine lt_of_le_of_lt ?_ hx
      rw [Nat.cast_add]
      exact add_le_add hsmall le_rfl
    exact Nat.cast_lt.mp h1
  · have h1 :
        (((Fintype.card ι + 1) * k - 1 + b : ℕ) : ENNReal) <
          ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
            ENNReal) := by
      refine lt_of_le_of_lt ?_ hx
      rw [Nat.cast_add]
      exact add_le_add hlarge le_rfl
    have h2 :
        (Fintype.card ι + 1) * k - 1 + b <
          (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :=
      Nat.cast_lt.mp h1
    have hMpos : 0 < (Fintype.card ι + 1) * k := Nat.mul_pos (Nat.succ_pos _) hk
    omega

/-- **§6 consumer for the exceptional-set residual** (the honest replacement for
`RS_jointAgreement_of_prob_gt_and_coeff_polys`).  The probability threshold `η` is
strengthened by the named card inequality `hη : k·errorBound·|F| + b ≤ η·|F|`, which makes
the good set large enough to absorb the exceptional set: `|good \ E| ≥ |good| - b` still
beats both counting thresholds, and the single-family subset core fires at
`S' = good \ E`. -/
theorem RS_jointAgreement_of_prob_gt_exc
    {k deg : ℕ} {domain : ι ↪ F} {δ η : ℝ≥0} [NeZero deg]
    (b : ℕ)
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] > (η : ENNReal))
    (hη :
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal) + (b : ENNReal) ≤
        (η : ENNReal) * (Fintype.card F : ENNReal))
    (hsmall :
      (k : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal))
    (hlarge :
      ((((Fintype.card ι + 1) * k : ℕ) - 1 : ℕ) : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal))
    (hcoeffPolyExc : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F, ∃ E : Finset F,
          E.card ≤ b ∧
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              z ∉ E → ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  obtain ⟨hGgt, hGge⟩ :=
    goodCoeffsCurve_card_bounds_of_prob_gt_exc
      (k := k) (deg := deg) (domain := domain) (δ := δ) (η := η)
      b hk u hprob hη hsmall hlarge
  obtain ⟨P, hP⟩ :=
    exists_decoded_polynomial_family_of_subset_goodCoeffsCurve
      (k := k) (deg := deg) (domain := domain) (δ := δ) u
      (S' := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
      (fun _ hz => hz)
  obtain ⟨B, E, hEcard, hBdeg, hBid⟩ := hcoeffPolyExc P hP
  have hsub :=
    Finset.le_card_sdiff E
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
  have hMpos : 0 < (Fintype.card ι + 1) * k := Nat.mul_pos (Nat.succ_pos _) hk
  refine subset_single_decoded_family_coeff_polys_implies_jointAgreement_of_pos
    (deg := deg) (domain := domain) (δ := δ) hk
    (S' := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ \ E)
    (by omega) (by omega) P ?_ B hBdeg ?_
  · intro z hz
    exact hP z (Finset.mem_sdiff.mp hz).1
  · intro z hz j hj
    have hz' := Finset.mem_sdiff.mp hz
    exact hBid z hz'.1 hz'.2 j hj

/-- `δ_ε_correlatedAgreementCurves` is antitone in the threshold direction: a statement at
proximity error `ε` implies the statement at any larger `ε'`. -/
theorem δ_ε_correlatedAgreementCurves_mono_error {k : ℕ}
    {C : Set (ι → F)} {δ ε ε' : ℝ≥0}
    (hεε' : ε ≤ ε')
    (h : δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := C) (δ := δ) (ε := ε)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := C) (δ := δ) (ε := ε') := by
  intro u hprob
  refine h u (lt_of_le_of_lt ?_ hprob)
  exact mul_le_mul_right (ENNReal.coe_le_coe.mpr hεε') _

/-- Strict-Johnson front door for the exceptional-set residual, at the explicit threshold
`k · (errorBound + b / |F|)`.  The extra `k · b / |F|` of probability mass converts to
`k·b ≥ b` surplus good parameters, which pays for the exceptional set. -/
theorem RS_jointAgreement_of_prob_gt_strict_johnson_exc
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (b : ℕ)
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) *
          ((errorBound δ deg domain + (b : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) :
            ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hcoeffPolyExc : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F, ∃ E : Finset F,
          E.card ≤ b ∧
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              z ∉ E → ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  set qn : ℝ≥0 := (Fintype.card F : ℝ≥0) with hqn
  have hqn0 : qn ≠ 0 := by
    simp [hqn, Fintype.card_ne_zero]
  set η : ℝ≥0 := (k : ℝ≥0) * (errorBound δ deg domain + (b : ℝ≥0) / qn) with hηdef
  have hprob' :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] > (η : ENNReal) := by
    simpa [hηdef, ENNReal.coe_mul, ENNReal.coe_natCast] using hprob
  have hk1 : (1 : ℝ≥0) ≤ (k : ℝ≥0) := by
    exact_mod_cast hk
  have hη_nn :
      (k : ℝ≥0) * errorBound δ deg domain * qn + (b : ℝ≥0) ≤ η * qn := by
    have hbq : (b : ℝ≥0) / qn * qn = (b : ℝ≥0) := div_mul_cancel₀ _ hqn0
    have hkey : η * qn =
        (k : ℝ≥0) * errorBound δ deg domain * qn + (k : ℝ≥0) * (b : ℝ≥0) := by
      calc η * qn
          = (k : ℝ≥0) *
              (errorBound δ deg domain * qn + (b : ℝ≥0) / qn * qn) := by
            rw [hηdef]; ring
        _ = (k : ℝ≥0) * (errorBound δ deg domain * qn + (b : ℝ≥0)) := by
            rw [hbq]
        _ = (k : ℝ≥0) * errorBound δ deg domain * qn + (k : ℝ≥0) * (b : ℝ≥0) := by
            ring
    rw [hkey]
    exact add_le_add le_rfl (le_mul_of_one_le_left (zero_le _) hk1)
  have hη :
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal) + (b : ENNReal) ≤
        (η : ENNReal) * (Fintype.card F : ENNReal) := by
    have hcast := ENNReal.coe_le_coe.mpr hη_nn
    simpa [hqn, ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_natCast] using hcast
  exact RS_jointAgreement_of_prob_gt_exc
    (deg := deg) (domain := domain) (δ := δ) (η := η)
    b hk u hprob' hη
    (prob_threshold_small_of_strict_johnson hk (Nat.pos_of_neZero deg) hδ)
    (prob_threshold_large_of_errorBound_ge_succ_const
      (errorBound_ge_succ_const_of_strict_johnson (deg := deg) (domain := domain) hJ hδ))
    hcoeffPolyExc

/-- **Theorem 1.5 from the exceptional-set residual** ([BCIKS20], honest §5 conclusion
shape; cf. BCHKS25 results 3–4).  Identical to
`correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary` except that the
strict Johnson branch consumes `StrictCoeffPolysExcResidual b` (which permits `≤ b`
exceptional parameters) and the proximity error pays for it:
`ε = errorBound δ deg domain + b / |F|`. -/
theorem correlatedAgreement_affine_curves_of_strict_coeff_polys_exc {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (b : ℕ)
    (_hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCoeffExc :
      StrictCoeffPolysExcResidual (k := k) (deg := deg) (domain := domain) (δ := δ) b)
    (hBoundary :
      BoundaryProbabilityResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ)
      (ε := errorBound δ deg domain + (b : ℝ≥0) / (Fintype.card F : ℝ≥0)) := by
  classical
  have hmono :
      errorBound δ deg domain ≤
        errorBound δ deg domain + (b : ℝ≥0) / (Fintype.card F : ℝ≥0) :=
    le_self_add
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact δ_ε_correlatedAgreementCurves_mono_error hmono
      (RS_correlatedAgreement_curves_k_zero (deg := deg) (domain := domain) (δ := δ))
  · by_cases hUDR : δ ≤ Code.relativeUniqueDecodingRadius (ι := ι) (F := F)
        (C := ReedSolomon.code domain deg)
    · exact δ_ε_correlatedAgreementCurves_mono_error hmono
        (RS_correlatedAgreement_curves_uniqueDecodingRegime hkpos hUDR)
    · unfold δ_ε_correlatedAgreementCurves
      intro u hprob
      have hprob_weak :
          Pr_{
            let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                ReedSolomon.code domain deg) ≤ δ] >
            ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) := by
        refine lt_of_le_of_lt ?_ hprob
        exact mul_le_mul_right (ENNReal.coe_le_coe.mpr hmono) _
      by_cases hJ :
          (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ
      · by_cases hsqrt : δ < 1 - ReedSolomon.sqrtRate deg domain
        · exact RS_jointAgreement_of_prob_gt_strict_johnson_exc
            (deg := deg) (domain := domain) (δ := δ) b hkpos u hprob hJ hsqrt
            (hStrictCoeffExc hkpos u hprob_weak hJ hsqrt)
        · exact hBoundary hkpos u hprob_weak hJ hsqrt
      · push Not at hJ
        exact False.elim (hUDR
          (RS_le_relativeUniqueDecodingRadius_of_le_rate_half
            (deg := deg) (domain := domain) (δ := δ) hJ))

/-- **Strict-interior exceptional-set front door.**  In the open Johnson regime
`δ < 1 - sqrtRate`, the boundary branch is unreachable, so the exceptional-set strict
coefficient residual gives the curve correlated-agreement theorem without any
`BoundaryProbabilityResidual` assumption. -/
theorem correlatedAgreement_affine_curves_strict_of_strict_coeff_polys_exc {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (b : ℕ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCoeffExc :
      StrictCoeffPolysExcResidual (k := k) (deg := deg) (domain := domain) (δ := δ) b) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ)
      (ε := errorBound δ deg domain + (b : ℝ≥0) / (Fintype.card F : ℝ≥0)) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys_exc
    (k := k) (deg := deg) (domain := domain) (δ := δ) b hδ.le hStrictCoeffExc
    (fun _hk _u _hprob _hJ hnot => absurd hδ hnot)

end ExceptionalResidual

end ProximityGap

#print axioms ProximityGap.subset_single_decoded_family_coeff_polys_implies_jointAgreement_core
#print axioms ProximityGap.subset_single_decoded_family_coeff_polys_implies_jointAgreement_of_pos
#print axioms ProximityGap.StrictCoeffPolysExcResidual
#print axioms ProximityGap.strictCoeffPolysExcResidual_of_strictCoeffPolysResidual
#print axioms ProximityGap.strictCoeffPolysResidual_of_strictCoeffPolysExcResidual_zero
#print axioms ProximityGap.goodCoeffsCurve_card_bounds_of_prob_gt_exc
#print axioms ProximityGap.RS_jointAgreement_of_prob_gt_exc
#print axioms ProximityGap.δ_ε_correlatedAgreementCurves_mono_error
#print axioms ProximityGap.RS_jointAgreement_of_prob_gt_strict_johnson_exc
#print axioms ProximityGap.correlatedAgreement_affine_curves_of_strict_coeff_polys_exc
#print axioms ProximityGap.correlatedAgreement_affine_curves_strict_of_strict_coeff_polys_exc

