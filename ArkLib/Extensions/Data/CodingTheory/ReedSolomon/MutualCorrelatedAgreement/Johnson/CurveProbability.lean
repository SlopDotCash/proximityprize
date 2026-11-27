/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude

Ported from mitschabaude-bot/ArkLib:reduced-rate (commit 93fd4833b88fb0b964a29d9ca8cbbcd7ca781ba4).
-/

import ArkLib.Extensions.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Curve
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.CurveBridge
import ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving

/-!
# Johnson mutual correlated agreement error for power curves

Over a finite field, the Johnson exceptional-set bound for power curves at the threshold
`⌈a n⌉₊`, with `a = √(D / n) + η`, bounds the mutual correlated agreement error of the univariate
powers generator `z ↦ (1, z, …, z ^ ℓ)` at radius `1 - a` by `min 1 (ℓ E₀ / |F|)`, where
`E₀ = johnsonExceptionCount n D ⌈a n⌉₊ η` is the affine-line count. The evaluation domain is an
arbitrary finite index type, and no characteristic hypothesis is needed. The same bound holds for
every row-wise interleaving of the code.

## Main statements

* `ReedSolomon.exists_johnson_curve_exactPowerAgreement_line_mul_of_fintype`: the exceptional-set
  bound on an arbitrary finite evaluation domain.
* `ReedSolomon.mcaError_univariatePowers_johnson_le`: the Johnson powers MCA error bound.
* `ReedSolomon.mcaError_univariatePowers_johnson_le_closed`: its closed form
  `ℓ · (8/3) n t³ / (ρ₋ |F|)`.
* `ReedSolomon.mcaError_univariatePowers_johnson_le_comparisonEstimate`: the bound with the
  constant of [BCHKS25] Theorem 4.6, `ℓ · johnsonComparisonEstimate n D η / |F|`.
* `ReedSolomon.mcaError_univariatePowers_interleaved_johnson_le`: the same bound for the
  interleaved code `code domain (D + 1) ^⋈ κ`.

## References

* [BCHKS25]
* [DKT26]
* [Jo26]
-/


namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode

section Reindex

variable {F : Type} [Field F] {ι : Type} [Fintype ι] {ℓ : ℕ}

/-- The exceptional-set bound of `exists_johnson_curve_exactPowerAgreement_line_mul` on an
arbitrary finite evaluation domain, by reindexing along `Fintype.equivFin`. -/
theorem exists_johnson_curve_exactPowerAgreement_line_mul_of_fintype [decF : DecidableEq F]
    {D A : ℕ} {eta : ℝ} (domain : ι ↪ F) (values : Fin (ℓ + 1) → ι → F)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (hthreshold : johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι ≤ A)
    (hAn : A ≤ Fintype.card ι) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ ℓ * johnsonExceptionCount (Fintype.card ι) D A eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF := Subsingleton.elim _ _
  cases hdec
  classical
  let e := (Fintype.equivFin ι).symm
  obtain ⟨ex, hcard, hgood⟩ := exists_johnson_curve_exactPowerAgreement_line_mul
    (e.toEmbedding.trans domain) (fun t ↦ values t ∘ e) hD hDn heta hℓ hthreshold hAn
  refine ⟨ex, hcard, fun z hz P hP hA ↦ ?_⟩
  apply ProximityGap.hasExactPowerAgreement_of_comp_equiv e domain values z P
  apply hgood z hz P hP
  change A ≤ (polynomialAgreementSet (e.toEmbedding.trans domain)
    (powerBatchedWord values z ∘ e) P).card
  rwa [ProximityGap.polynomialAgreementSet_card_comp_equiv]

end Reindex

section Probability

variable {F : Type} [Field F] [Fintype F] [SampleableType F] {ι : Type} [Fintype ι] {ℓ : ℕ}

/-- **Johnson powers MCA error.** For a Reed–Solomon code of dimension `D + 1` on any `n`
evaluation points over a finite field, `ℓ ≥ 1` and `a = √(D / n) + η ≤ 1`, the MCA error of the
univariate powers generator `z ↦ (1, z, …, z ^ ℓ)` at radius `1 - a` is at most
`min 1 (ℓ · johnsonExceptionCount n D ⌈a n⌉₊ η / |F|)`. -/
theorem mcaError_univariatePowers_johnson_le {D : ℕ} {eta : ℝ} (domain : ι ↪ F)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1) :
    mcaError (univariatePowersGenerator F ℓ) (code domain (D + 1))
        (1 - johnsonAgreement (Fintype.card ι) D eta) ≤
      min 1 (ENNReal.ofReal (ℓ * johnsonExceptionCount (Fintype.card ι) D
        ⌈johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι⌉₊ eta /
          (Fintype.card F : ℝ))) := by
  classical
  set n := Fintype.card ι
  set A := ⌈johnsonAgreement n D eta * n⌉₊
  have hAn : A ≤ n := Nat.ceil_le.mpr (by nlinarith [Nat.cast_nonneg n (α := ℝ)])
  refine le_min (mcaError_le_one _ _ _) ?_
  refine ProximityGap.mcaError_powers_le_of_exactPowerAgreement (D + 1) domain ℓ A _ _ ?_
    (fun w ↦ exists_johnson_curve_exactPowerAgreement_line_mul_of_fintype domain w hD hDn heta hℓ
      (Nat.le_ceil _) hAn)
  rw [show (n : ℝ) * (1 - (1 - johnsonAgreement n D eta)) = johnsonAgreement n D eta * n by ring]

/-- **Johnson powers MCA error, closed form.** Under the hypotheses of
`mcaError_univariatePowers_johnson_le`, the MCA error of the univariate powers generator of degree
`ℓ` at radius `1 - a` is at most `ℓ · (8/3) n t³ / (ρ₋ |F|)`, with `t = johnsonT n D η` and
`ρ₋ = D / n`. -/
theorem mcaError_univariatePowers_johnson_le_closed {D : ℕ} {eta : ℝ} (domain : ι ↪ F)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1) :
    mcaError (univariatePowersGenerator F ℓ) (code domain (D + 1))
        (1 - johnsonAgreement (Fintype.card ι) D eta) ≤
      ENNReal.ofReal (ℓ * ((8 / 3 : ℝ) * Fintype.card ι * johnsonT (Fintype.card ι) D eta ^ 3 /
        johnsonRhoMinus (Fintype.card ι) D) / (Fintype.card F : ℝ)) := by
  refine (mcaError_univariatePowers_johnson_le domain hD hDn heta hℓ ha).trans
    ((min_le_right _ _).trans (ENNReal.ofReal_le_ofReal ?_))
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (johnsonExceptionCount_lt_closed hD hDn heta
    (Nat.le_ceil _)).le (Nat.cast_nonneg _)

/-- **Johnson powers MCA error with the [BCHKS25] constant.** Under the hypotheses of
`mcaError_univariatePowers_johnson_le`, the MCA error of the univariate powers generator of degree
`ℓ` at radius `1 - a` is at most `ℓ` times the Johnson exception estimate
`johnsonComparisonEstimate n D η / |F|`, the constant of [BCHKS25] Theorem 4.6 at curve
degree `ℓ`. -/
theorem mcaError_univariatePowers_johnson_le_comparisonEstimate {D : ℕ} {eta : ℝ}
    (domain : ι ↪ F)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1) :
    mcaError (univariatePowersGenerator F ℓ) (code domain (D + 1))
        (1 - johnsonAgreement (Fintype.card ι) D eta) ≤
      ENNReal.ofReal (ℓ * johnsonComparisonEstimate (Fintype.card ι) D eta /
        (Fintype.card F : ℝ)) := by
  refine (mcaError_univariatePowers_johnson_le domain hD hDn heta hℓ ha).trans
    ((min_le_right _ _).trans (ENNReal.ofReal_le_ofReal ?_))
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (johnsonExceptionCount_le_comparisonEstimate hDn heta ha
    (Nat.le_ceil _)) (Nat.cast_nonneg _)

/-- **Johnson powers MCA error for interleaved codes.** The bound of
`mcaError_univariatePowers_johnson_le` holds for the row-wise interleaving
`code domain (D + 1) ^⋈ κ` with any finite row type `κ`: the seed space of the powers generator
is the field, so interleaving does not increase the MCA error. -/
theorem mcaError_univariatePowers_interleaved_johnson_le {κ : Type} [Finite κ] {D : ℕ}
    {eta : ℝ} (domain : ι ↪ F)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1) :
    mcaError (univariatePowersGenerator F ℓ)
        ((code domain (D + 1) : ModuleCode ι F F)^⋈κ)
        (1 - johnsonAgreement (Fintype.card ι) D eta) ≤
      min 1 (ENNReal.ofReal (ℓ * johnsonExceptionCount (Fintype.card ι) D
        ⌈johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι⌉₊ eta /
          (Fintype.card F : ℝ))) :=
  (mcaError_moduleInterleavedCode_le_of_card_le _ _ _ le_rfl).trans
    (mcaError_univariatePowers_johnson_le domain hD hDn heta hℓ ha)

end Probability

end ReedSolomon

#print axioms ReedSolomon.exists_johnson_curve_exactPowerAgreement_line_mul_of_fintype
#print axioms ReedSolomon.mcaError_univariatePowers_johnson_le
#print axioms ReedSolomon.mcaError_univariatePowers_johnson_le_closed
#print axioms ReedSolomon.mcaError_univariatePowers_johnson_le_comparisonEstimate
#print axioms ReedSolomon.mcaError_univariatePowers_interleaved_johnson_le
