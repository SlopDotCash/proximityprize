/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StrictCoeffPolysShare

/-!
# BCIKS20 §5 — the disjunctive share residual (#304, leg-4 surface)

The cell machinery produces decode witnesses (`McaDecodeCurve`) only in the MCA *bad*
event: the per-`γ` witness carries the `hnjp` clause (*no* codeword stack jointly agrees
on the witness set), which is **underivable** when `jointAgreement` already holds.  So
the honest producer-facing surface is disjunctive: at each instance, EITHER the stack
already agrees jointly (and the §6 consumer is done outright), OR the share-form
coefficient extraction fires.

* `StrictCoeffPolysShareResidualOr ℓ T` — verbatim `StrictCoeffPolysShareResidual`,
  except the conclusion allows the `jointAgreement` escape;
* `strictCoeffPolysResidualShareOr_of_share` — the non-disjunctive form lands in it;
* `RS_jointAgreement_of_prob_gt_strict_johnson_share_or` — the §6 consumer: the escape
  branch is the goal itself, the share branch runs the landed share consumer;
* `correlatedAgreement_affine_curves_of_strict_coeff_polys_share_or` /
  `correlatedAgreement_affine_curves_strict_of_strict_coeff_polys_share_or` — Theorem 1.5
  from the disjunctive residual, same proximity error as the share form
  (`ε = errorBound + (ℓ·(n+1)·k + T)/|F|`); the strict-interior door carries no boundary
  residual.

This makes the disjunctive surface **consumer-equivalent** to the share surface, while
being the exact shape a `McaDecodeCurve`-based producer can discharge (see
`Hab25ShareGoodSetWeld.lean` for the decode-witness construction under
`¬ jointAgreement`).
-/

namespace ProximityGap

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory ENNReal
open Code

section ShareOrResidual

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Disjunctive share-form strict Johnson extraction residual.**  Verbatim
`StrictCoeffPolysShareResidual`, except the conclusion allows the `jointAgreement`
escape — the branch in which no MCA decode witness (with its `hnjp` clause) exists, and
in which the §6 consumer needs nothing further. -/
def StrictCoeffPolysShareResidualOr {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (ℓ T : ℕ) : Prop :=
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
        jointAgreement (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
          (W := u) ∨
        ∃ B : ℕ → Polynomial F, ∃ G' : Finset F,
          G' ⊆ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ ∧
          (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≤
            T + ℓ * G'.card ∧
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ G', ∀ j < deg, (P z).coeff j = (B j).eval z

/-- The non-disjunctive share residual lands in the disjunctive one. -/
theorem strictCoeffPolysResidualShareOr_of_share
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} {ℓ T : ℕ}
    (h : StrictCoeffPolysShareResidual (k := k) (deg := deg) (domain := domain) (δ := δ)
      ℓ T) :
    StrictCoeffPolysShareResidualOr (k := k) (deg := deg) (domain := domain) (δ := δ)
      ℓ T :=
  fun hk u hprob hJ hsqrt P hP => Or.inr (h hk u hprob hJ hsqrt P hP)

/-- Strict-Johnson front door for the disjunctive share residual, at the same explicit
threshold as the share form.  The escape branch IS the goal; the share branch runs the
landed share consumer. -/
theorem RS_jointAgreement_of_prob_gt_strict_johnson_share_or
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (ℓ T : ℕ)
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) *
          ((errorBound δ deg domain +
            ((ℓ * ((Fintype.card ι + 1) * k) + T : ℕ) : ℝ≥0) /
              (Fintype.card F : ℝ≥0) : ℝ≥0) :
            ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hOr :
      jointAgreement (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
        (W := u) ∨
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F, ∃ G' : Finset F,
            G' ⊆ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ ∧
            (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≤
              T + ℓ * G'.card ∧
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ G', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  rcases hOr with hJA | hShare
  · exact hJA
  · exact RS_jointAgreement_of_prob_gt_strict_johnson_share
      (deg := deg) (domain := domain) (δ := δ) ℓ T hk u hprob hJ hδ hShare

/-- **Theorem 1.5 from the disjunctive share residual**, at the same proximity error as
the share form: `ε = errorBound + (ℓ·(n+1)·k + T)/|F|`. -/
theorem correlatedAgreement_affine_curves_of_strict_coeff_polys_share_or {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (ℓ T : ℕ)
    (_hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hShareOr :
      StrictCoeffPolysShareResidualOr (k := k) (deg := deg) (domain := domain) (δ := δ)
        ℓ T)
    (hBoundary :
      BoundaryProbabilityResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ)
      (ε := errorBound δ deg domain +
        ((ℓ * ((Fintype.card ι + 1) * k) + T : ℕ) : ℝ≥0) /
          (Fintype.card F : ℝ≥0)) := by
  classical
  have hmono :
      errorBound δ deg domain ≤
        errorBound δ deg domain +
          ((ℓ * ((Fintype.card ι + 1) * k) + T : ℕ) : ℝ≥0) /
            (Fintype.card F : ℝ≥0) :=
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
        · rcases hShareOr hkpos u hprob_weak hJ hsqrt with hres
          -- split on whether the residual escaped at the canonical decoded family;
          -- both branches feed the disjunctive front door
          refine RS_jointAgreement_of_prob_gt_strict_johnson_share_or
            (deg := deg) (domain := domain) (δ := δ) ℓ T hkpos u hprob hJ hsqrt ?_
          by_cases hJA : jointAgreement
              (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ) (W := u)
          · exact Or.inl hJA
          · refine Or.inr ?_
            intro P hP
            rcases hres P hP with hJA' | hB
            · exact absurd hJA' hJA
            · exact hB
        · exact hBoundary hkpos u hprob_weak hJ hsqrt
      · push Not at hJ
        exact False.elim (hUDR
          (RS_le_relativeUniqueDecodingRadius_of_le_rate_half
            (deg := deg) (domain := domain) (δ := δ) hJ))

/-- **Strict-interior disjunctive front door.**  In the open Johnson regime the boundary
branch is unreachable. -/
theorem correlatedAgreement_affine_curves_strict_of_strict_coeff_polys_share_or {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (ℓ T : ℕ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hShareOr :
      StrictCoeffPolysShareResidualOr (k := k) (deg := deg) (domain := domain) (δ := δ)
        ℓ T) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ)
      (ε := errorBound δ deg domain +
        ((ℓ * ((Fintype.card ι + 1) * k) + T : ℕ) : ℝ≥0) /
          (Fintype.card F : ℝ≥0)) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys_share_or
    (k := k) (deg := deg) (domain := domain) (δ := δ) ℓ T hδ.le hShareOr
    (fun _hk _u _hprob _hJ hnot => absurd hδ hnot)

end ShareOrResidual

end ProximityGap

/-! ## Axiom audit — all kernel-clean. -/
#print axioms ProximityGap.StrictCoeffPolysShareResidualOr
#print axioms ProximityGap.strictCoeffPolysResidualShareOr_of_share
#print axioms ProximityGap.RS_jointAgreement_of_prob_gt_strict_johnson_share_or
#print axioms ProximityGap.correlatedAgreement_affine_curves_of_strict_coeff_polys_share_or
#print axioms ProximityGap.correlatedAgreement_affine_curves_strict_of_strict_coeff_polys_share_or
