/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.UniqueDecoding
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.BoundaryCardResidual
import ArkLib.ToMathlib.BoundaryDischarge
import ArkLib.ToMathlib.KeystoneStrictResidual

/-!
# BCIKS20 Theorem 1.4 — correlated agreement of Reed-Solomon codes over affine lines

This file assembles the main correlated-agreement theorem of [BCIKS20] over affine lines from
the unique-decoding and curve ingredients. `RS_correlatedAgreement_affineLines` (and its strict /
positive variants `RS_correlatedAgreement_affineLines_strict`,
`RS_correlatedAgreement_affineLines_strict_pos`) cover the regime up to the relevant bound, while
the `..._johnson_of_betaRec...` results extend the conclusion into the Johnson regime, conditional
on the recursive `β`-construction and the documented lattice residual.
-/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Finset Code
open scoped BigOperators LinearCode

universe u v w k l

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
/-- Theorem 1.4 (Main Theorem — Correlated agreement over lines) in [BCIKS20].
Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and two words `u₀` and `u₁`, such that the probability that a random affine
line passing through `u₀` and `u₁` is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u₀` and `u₁` have correlated agreement.

This is the `k = 1` affine-line specialization of the curves keystone
`correlatedAgreement_affine_curves`. Following that keystone, the two list-decoding
residuals are threaded as explicit hypotheses, specialized to `k = 1`:
* `hStrictCoeff` is the [BCIKS20] §5 strict Johnson-branch coefficient-polynomial
  extraction obligation (`StrictCoeffPolysResidual`);
* `hBoundaryCard` is the [BCIKS20] §6.2 closed square-root boundary assembly
  obligation (`BoundaryCardResidual`). -/
theorem RS_correlatedAgreement_affineLines {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    -- Match the curves theorem: at `deg = 0`, the Johnson-branch error bound
    -- can make the list-decoding branch too weak for this statement.
    [NeZero deg]
    -- [BCIKS20] §5: strict Johnson-branch coefficient-polynomial extraction residual,
    -- specialized to the `k = 1` affine line.
    (hStrictCoeff : StrictCoeffPolysResidual (k := 1) (deg := deg) (domain := domain) (δ := δ))
    -- [BCIKS20] §6.2: closed square-root boundary assembly residual,
    -- specialized to the `k = 1` affine line.
    (hBoundaryCard : BoundaryCardResidual (k := 1) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - (ReedSolomon.sqrtRate deg domain)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  -- Do casing analysis on `hδ`
  by_cases hδ_uniqueDecodingRegime :
    δ ≤ Code.relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg)
  · exact RS_correlatedAgreement_affineLines_uniqueDecodingRegime (hδ := hδ_uniqueDecodingRegime)
  · classical
    have hcurves := correlatedAgreement_affine_curves_of_boundaryCardResidual (k := 1) (deg := deg)
      (domain := domain) (δ := δ) hStrictCoeff hBoundaryCard hδ
    unfold δ_ε_correlatedAgreementAffineLines
    intro u hprob
    unfold δ_ε_correlatedAgreementCurves at hcurves
    exact hcurves u (by
      simpa [one_mul, Fin.sum_univ_two] using hprob)

omit [DecidableEq ι] in
/-- Strict square-root-radius affine-line capstone. In the strict range, the closed-boundary
residual branch of the curves theorem is impossible, so only the strict coefficient-polynomial
extraction residual is needed. -/
theorem RS_correlatedAgreement_affineLines_strict {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hStrictCoeff : StrictCoeffPolysResidual (k := 1) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  have hcurves := correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := 1) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP => hStrictCoeff hk u hprob hJ hδ P hP)
  unfold δ_ε_correlatedAgreementAffineLines
  intro u hprob
  unfold δ_ε_correlatedAgreementCurves at hcurves
  exact hcurves u (by
    simpa [one_mul, Fin.sum_univ_two] using hprob)

omit [DecidableEq ι] in
/-- Strict positive-radius affine-line capstone. This is the positive-`δ` API form used by
the BCIKS20 proximity-gap statements; the current proof only needs the strict square-root
upper bound, so the positivity hypothesis is retained as a harmless interface adapter. -/
theorem RS_correlatedAgreement_affineLines_strict_pos {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (_hδ_pos : 0 < δ)
    (hStrictCoeff : StrictCoeffPolysResidual (k := 1) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_strict (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ) hStrictCoeff hδ

omit [DecidableEq ι] in
/-- Strict square-root-radius affine-line capstone with the §5 Johnson branch supplied by the
verified `betaRec` capsule. This is the affine-line public front door corresponding to
`KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec_strict`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_strict
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInput
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_strict (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    hδ

omit [DecidableEq ι] in
/-- Strict square-root-radius affine-line capstone with the §5 Johnson branch supplied by the
off-centre local-variable `betaRec` capsule. This is the affine-line public front door
corresponding to
`KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec_offcentre_strict`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_strict
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_strict (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec_offcentre
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    hδ

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the §5 Johnson branch supplied by the off-centre
local-variable `betaRec` capsule and the boundary branch supplied as the already-packaged
`BoundaryCardResidual`.

This is the affine-line counterpart of
`KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec_offcentre`, specialized
to `k = 1`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryCard :
      BoundaryCardResidual (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec_offcentre
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    hBoundaryCard hδ

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the strict Johnson branch supplied by the verified
`betaRec` capsule and the square-root boundary branch supplied by explicit boundary cardinality
and coefficient-polynomial data. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInput
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryData : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ).card →
      ((RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ).card > 1) ∧
      ((RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * 1) ∧
      (∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < 2) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    (ArkLib.BoundaryDischarge.boundaryCardResidual_of_boundary_cards_and_coeffPolys
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundaryData)
    hδ

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the strict Johnson branch supplied by the verified
`betaRec` capsule and the square-root boundary reduced by the quantization split in
`BoundaryCardResidual.lean`.

Compared with `RS_correlatedAgreement_affineLines_johnson_of_betaRec`, this consumes the smaller
boundary surface:
* a strict-subradius positive-good-set producer for the non-lattice boundary levels;
* the isolated lattice residual `BoundaryCardLatticeResidual` for the exact `1/n` boundary points.
-/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_lattice_residual
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInput
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLattice :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeResidual
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    (ArkLib.BoundaryCardResidual.boundaryCardResidual_of_lattice_residual
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLattice hStrictBoundary)
    hδ

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the exact lattice branch supplied through
`BoundaryCardLatticeData`.

This is the adapter-only front door for callers that have reduced the genuine `1/n` lattice case
to concrete good-set cardinality and coefficient-polynomial data, rather than the older
`BoundaryCardLatticeResidual` surface.  The non-lattice boundary levels are still handled by
`hStrictBoundary`; this theorem does not prove or assume the exact lattice data. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_lattice_data
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInput
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLatticeData :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_lattice_residual
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hInput hStrictBoundary
    (ArkLib.BoundaryDischarge.boundaryCardLatticeResidual_of_lattice_data
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLatticeData)

omit [DecidableEq ι] in
/-- Square-endpoint affine-line capstone with the strict Johnson branch supplied by the verified
`betaRec` capsule and the exact lattice branch supplied through `BoundaryCardLatticeData`.

Compared with `RS_correlatedAgreement_affineLines_johnson_of_betaRec_lattice_data`, this
square-endpoint adapter does not require the strict-interior boundary producer: once
`deg * |ι|` is a square, the closed boundary is exactly the isolated lattice-data branch. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_lattice_data_isSquare
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hSquare : IsSquare (deg * Fintype.card ι))
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInput
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hLatticeData :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  have hcurves :=
    ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_lattice_data_isSquare
      (k := 1) (deg := deg) (domain := domain) (δ := δ)
      (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec
        (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
      hLatticeData hδ hsqrt_le hdeg hSquare
  unfold δ_ε_correlatedAgreementAffineLines
  intro u hprob
  unfold δ_ε_correlatedAgreementCurves at hcurves
  exact hcurves u (by
    simpa [one_mul, Fin.sum_univ_two] using hprob)

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the strict Johnson branch supplied by the verified
`betaRec` capsule and the complete square-root boundary quantization package.

This is a data-facing adapter over
`RS_correlatedAgreement_affineLines_johnson_of_betaRec_lattice_data`: the non-lattice
strict-subradius producer and exact lattice data are projected from `BoundaryCardQuantizationData`.
-/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_quantization_data
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInput
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundary :
      ArkLib.BoundaryDischarge.BoundaryCardQuantizationData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_lattice_data
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hInput
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.strictInterior
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.latticeData
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the §5 Johnson branch supplied by the off-centre
local-variable `betaRec` capsule and the boundary branch supplied as a `BoundaryCardResidual`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_boundaryCard
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryCard : BoundaryCardResidual (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec_offcentre
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    hBoundaryCard hδ

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with off-centre `betaRec` and the exact boundary branch
supplied as `BoundaryCardLatticeResidual`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_lattice_residual
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLattice :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeResidual
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_boundaryCard
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ) hδ hInput
    (ArkLib.BoundaryCardResidual.boundaryCardResidual_of_lattice_residual
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLattice hStrictBoundary)

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with off-centre `betaRec` and concrete square-lattice
boundary data. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_lattice_data
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLatticeData :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_lattice_residual
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hInput hStrictBoundary
    (ArkLib.BoundaryDischarge.boundaryCardLatticeResidual_of_lattice_data
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLatticeData)

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with off-centre `betaRec` and the full boundary
quantization data package. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_quantization_data
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundary :
      ArkLib.BoundaryDischarge.BoundaryCardQuantizationData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_lattice_data
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hInput
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.strictInterior
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.latticeData
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)

omit [DecidableEq ι] in
/-- Square-endpoint affine-line capstone with the strict Johnson branch supplied by the verified
`betaRec` capsule and the boundary branch supplied by the complete quantization-data package.

This square-specific adapter projects only the exact lattice data from
`BoundaryCardQuantizationData`, because the strict-interior branch is not needed once the endpoint
is known to be the perfect-square lattice case. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_quantization_data_isSquare
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hSquare : IsSquare (deg * Fintype.card ι))
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInput
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundary :
      ArkLib.BoundaryDischarge.BoundaryCardQuantizationData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_lattice_data_isSquare
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hsqrt_le hdeg hSquare hInput
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.latticeData
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)

omit [DecidableEq ι] in
/-- Strict square-root-radius affine-line capstone with the §5 Johnson branch supplied by the
finite-range `betaRec` capsule. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRecFin_strict
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_strict (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRecFin
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    hδ

omit [DecidableEq ι] in
/-- Strict square-root-radius affine-line capstone with the §5 Johnson branch supplied by the
finite-range off-centre local-variable `betaRec` capsule. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_strict
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentreFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_strict (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec_offcentreFin
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    hδ

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the finite off-centre `betaRec` capsule and the
boundary branch supplied as the already-packaged `BoundaryCardResidual`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentreFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryCard :
      BoundaryCardResidual (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec_offcentreFin
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    hBoundaryCard hδ

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the strict Johnson branch supplied by the
finite-range `betaRec` capsule and the square-root boundary branch supplied by explicit boundary
cardinality and coefficient-polynomial data. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRecFin
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryData : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ).card →
      ((RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ).card > 1) ∧
      ((RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * 1) ∧
      (∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < 2) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRecFin
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    (ArkLib.BoundaryDischarge.boundaryCardResidual_of_boundary_cards_and_coeffPolys
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundaryData)
    hδ

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the strict Johnson branch supplied by the
finite-range `betaRec` capsule and the square-root boundary reduced by the quantization split in
`BoundaryCardResidual.lean`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRecFin_lattice_residual
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLattice :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeResidual
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRecFin
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    (ArkLib.BoundaryCardResidual.boundaryCardResidual_of_lattice_residual
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLattice hStrictBoundary)
    hδ

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the finite-range `betaRec` capsule and the exact
lattice branch supplied through `BoundaryCardLatticeData`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRecFin_lattice_data
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLatticeData :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRecFin_lattice_residual
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hInput hStrictBoundary
    (ArkLib.BoundaryDischarge.boundaryCardLatticeResidual_of_lattice_data
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLatticeData)

omit [DecidableEq ι] in
/-- Square-endpoint affine-line capstone with the finite-range `betaRec` capsule and the exact
lattice branch supplied through `BoundaryCardLatticeData`.

This is the finite-range companion to
`RS_correlatedAgreement_affineLines_johnson_of_betaRec_lattice_data_isSquare`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRecFin_lattice_data_isSquare
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hSquare : IsSquare (deg * Fintype.card ι))
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hLatticeData :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  have hcurves :=
    ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_lattice_data_isSquare
      (k := 1) (deg := deg) (domain := domain) (δ := δ)
      (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRecFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
      hLatticeData hδ hsqrt_le hdeg hSquare
  unfold δ_ε_correlatedAgreementAffineLines
  intro u hprob
  unfold δ_ε_correlatedAgreementCurves at hcurves
  exact hcurves u (by
    simpa [one_mul, Fin.sum_univ_two] using hprob)

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the finite-range `betaRec` capsule and the complete
square-root boundary quantization package.

This is the finite-range companion to
`RS_correlatedAgreement_affineLines_johnson_of_betaRec_quantization_data`, projecting both
boundary branches from `BoundaryCardQuantizationData`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRecFin_quantization_data
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundary :
      ArkLib.BoundaryDischarge.BoundaryCardQuantizationData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRecFin_lattice_data
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hInput
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.strictInterior
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.latticeData
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with the finite off-centre local-variable `betaRec`
capsule and the boundary branch supplied as a `BoundaryCardResidual`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_boundaryCard
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentreFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryCard : BoundaryCardResidual (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec_offcentreFin
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    hBoundaryCard hδ

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with finite off-centre `betaRec` and the exact boundary
branch supplied as `BoundaryCardLatticeResidual`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_lattice_residual
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentreFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLattice :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeResidual
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_boundaryCard
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ) hδ hInput
    (ArkLib.BoundaryCardResidual.boundaryCardResidual_of_lattice_residual
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLattice hStrictBoundary)

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with finite off-centre `betaRec` and concrete
square-lattice boundary data. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_lattice_data
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentreFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLatticeData :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_lattice_residual
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hInput hStrictBoundary
    (ArkLib.BoundaryDischarge.boundaryCardLatticeResidual_of_lattice_data
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLatticeData)

omit [DecidableEq ι] in
/-- Closed-boundary affine-line capstone with finite off-centre `betaRec` and the full boundary
quantization data package. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_quantization_data
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentreFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundary :
      ArkLib.BoundaryDischarge.BoundaryCardQuantizationData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_lattice_data
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hInput
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.strictInterior
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.latticeData
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)

omit [DecidableEq ι] in
/-- Square-endpoint affine-line capstone with the finite-range `betaRec` capsule and the boundary
branch supplied by the complete quantization-data package.

This is the finite-range companion to
`RS_correlatedAgreement_affineLines_johnson_of_betaRec_quantization_data_isSquare`. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRecFin_quantization_data_isSquare
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hSquare : IsSquare (deg * Fintype.card ι))
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundary :
      ArkLib.BoundaryDischarge.BoundaryCardQuantizationData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRecFin_lattice_data_isSquare
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hsqrt_le hdeg hSquare hInput
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.latticeData
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)

end CoreResults

end ProximityGap

#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_quantization_data
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_quantization_data_isSquare
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_lattice_data_isSquare
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_strict
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_boundaryCard
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_lattice_residual
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_lattice_data
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_quantization_data
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRecFin_quantization_data
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRecFin_quantization_data_isSquare
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRecFin_lattice_data_isSquare
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_strict
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_boundaryCard
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_lattice_residual
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_lattice_data
#print axioms
  ProximityGap.RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_quantization_data
