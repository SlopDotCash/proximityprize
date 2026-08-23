/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.CoeffExtractionVacuous
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.Main

/-!
# Issue #304 — UNCONDITIONAL BCIKS20 correlated agreement in the vacuous regime

Composes the vacuous-regime `StrictCoeffPolysResidual` discharges
(`CoeffExtractionVacuous.lean`) with the strict-radius capstones
(`RS_correlatedAgreement_affineLines_strict`,
`correlatedAgreement_affine_curves_of_strict_coeff_polys` — at strict `δ < 1 − √ρ` the closed
boundary branch is impossible, so the §6.2 boundary residual is not needed). The results are the
first **hypothesis-free** in-tree instances of the BCIKS20 correlated-agreement theorems:

* `RS_correlatedAgreement_affineLines_of_card_le` / `…_of_card_le_e7` — **Theorem 1.4 (lines)**
  for every field with `q ≤ n` resp. `q ≤ deg²·10⁷`;
* `correlatedAgreement_affine_curves_of_card_le` / `…_of_card_le_e7` — the affine-curves form for
  `q ≤ k·n` resp. `q ≤ k·deg²·10⁷`.

## Honest scope

In this regime `errorBound ≥ 1/k` (resp. `≥ 1`), so the correlated-agreement conclusions are
satisfied for threshold reasons — the statements are the genuine paper theorems, proven in the
parameter band where their probability thresholds are unsatisfiable. The deployed large-field band
(`q > k·max(n, deg²·10⁷)`) remains the open #304 content (the `BetaCurveInputFin` production).
Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code Polynomial
open scoped BigOperators LinearCode ProbabilityTheory ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Unconditional BCIKS20 Theorem 1.4 (affine lines), small-field regime `q ≤ n`.**
No residual hypotheses: the §5 extraction is vacuously discharged (`errorBound ≥ n/q ≥ 1`)
and the closed boundary is impossible at strict `δ`. -/
theorem RS_correlatedAgreement_affineLines_of_card_le {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hq : (Fintype.card F : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0)) :
    δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_strict
    (strictCoeffPolysResidual_of_card_le (k := 1)
      (Nat.pos_of_ne_zero (NeZero.ne deg)) hδ (by simpa [Nat.cast_one, one_mul] using hq))
    hδ

/-- **Unconditional BCIKS20 Theorem 1.4 (affine lines), sharp interior regime `q ≤ deg²·10⁷`.** -/
theorem RS_correlatedAgreement_affineLines_of_card_le_e7 {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0)) :
    δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_strict
    (strictCoeffPolysResidual_of_card_le_e7 (k := 1)
      (by simpa [Nat.cast_one, one_mul] using hq))
    hδ

/-- **Unconditional BCIKS20 affine-curves correlated agreement, small-field regime `q ≤ k·n`.** -/
theorem correlatedAgreement_affine_curves_of_card_le {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hq : (Fintype.card F : ℝ≥0) ≤ (k : ℝ≥0) * (Fintype.card ι : ℝ≥0)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  have hres := strictCoeffPolysResidual_of_card_le (k := k)
    (Nat.pos_of_ne_zero (NeZero.ne deg)) hδ hq
  exact correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP => hres hk u hprob hJ hδ P hP)

/-- **Unconditional BCIKS20 affine-curves correlated agreement, sharp interior `q ≤ k·deg²·10⁷`.** -/
theorem correlatedAgreement_affine_curves_of_card_le_e7 {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hq : (Fintype.card F : ℝ≥0) ≤ (k : ℝ≥0) * ((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  have hres := strictCoeffPolysResidual_of_card_le_e7 (k := k) (deg := deg) (domain := domain) (δ := δ) hq
  exact correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP => hres hk u hprob hJ hδ P hP)

end ProximityGap

#print axioms ProximityGap.RS_correlatedAgreement_affineLines_of_card_le
#print axioms ProximityGap.RS_correlatedAgreement_affineLines_of_card_le_e7
#print axioms ProximityGap.correlatedAgreement_affine_curves_of_card_le
#print axioms ProximityGap.correlatedAgreement_affine_curves_of_card_le_e7
