/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.CorrelatedAgreementSmallField
import ArkLib.ProofSystem.Whir.KeystoneReduction

/-!
# Issues #302/#303 — unconditional per-round keystone CA bounds (vacuous regime)

Composes the unconditional BCIKS20 correlated-agreement instances
(`CorrelatedAgreementSmallField.lean`, #304) through the numeric bridge
`δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le` (Errors.lean): the §1.1 per-round keystone
bound `epsCA_curves ≤ k · errorBound` — the exact quantity the WHIR keystone reduction and the
FRI `roundError` accounting consume — with **no residual hypotheses**, for every field with
`q ≤ k·n` (`keystone_curves_bound_of_card_le`) resp. `q ≤ k·deg²·10⁷` (`…_e7`).

Honest scope: threshold-vacuous regime (`errorBound ≥ 1/k` there); the deployed large-field band
remains the open #304 content. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code Polynomial
open scoped BigOperators LinearCode ProbabilityTheory ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Unconditional per-round CA numeric bound (small-field `q ≤ k·n`).** The §1.1 keystone
`epsCA_curves ≤ k·errorBound` with NO residual hypotheses, in the vacuous regime. -/
theorem keystone_curves_bound_of_card_le {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hq : (Fintype.card F : ℝ≥0) ≤ (k : ℝ≥0) * (Fintype.card ι : ℝ≥0)) :
    epsCA_curves (F := F) (ReedSolomon.code domain deg : Set (ι → F)) k δ δ ≤
      ((k * errorBound δ deg domain : ℝ≥0) : ENNReal) :=
  (δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le (F := F) (k := k)
    (C := (ReedSolomon.code domain deg : Set (ι → F))) δ (errorBound δ deg domain)).mp
    (correlatedAgreement_affine_curves_of_card_le hδ hq)

/-- **Unconditional per-round CA numeric bound (sharp interior `q ≤ k·deg²·10⁷`).** -/
theorem keystone_curves_bound_of_card_le_e7 {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hq : (Fintype.card F : ℝ≥0) ≤ (k : ℝ≥0) * ((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0)) :
    epsCA_curves (F := F) (ReedSolomon.code domain deg : Set (ι → F)) k δ δ ≤
      ((k * errorBound δ deg domain : ℝ≥0) : ENNReal) :=
  (δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le (F := F) (k := k)
    (C := (ReedSolomon.code domain deg : Set (ι → F))) δ (errorBound δ deg domain)).mp
    (correlatedAgreement_affine_curves_of_card_le_e7 hδ hq)

end ProximityGap

#print axioms ProximityGap.keystone_curves_bound_of_card_le
#print axioms ProximityGap.keystone_curves_bound_of_card_le_e7
