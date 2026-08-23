/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.MutualCorrAgreement

/-! # `mca_johnson_bound_CONJECTURE` holds in the small-field regime (verified sufficient condition).

Unlike the capacity conjecture, the Johnson conjecture's `errStar` is a FIXED sub-1 bound (no `∃`
constants), so it genuinely encodes the open Johnson-radius proximity gap. This file proves the one
regime that IS elementary: when `|F| ≤ (parℓ-1)·2^{2m}·10^7`, `errStar δ ≥ 1` for every admissible
`δ`, so `Pr ≤ 1 ≤ errStar δ` holds vacuously. The genuine content is the LARGE-field case, where
`errStar < 1` and Johnson list-decoding combinatorics bite.

Key: `min_val = min(1-√ρ-δ, √ρ/20) ≤ √ρ/20 ≤ 1/20`, so `(2·min_val)^7 ≤ (1/10)^7 = 10^{-7}`, hence
`errStar δ = (parℓ-1)2^{2m}/(|F|·(2 min_val)^7) ≥ (parℓ-1)2^{2m}·10^7/|F| ≥ 1`.
(Status correction 2026-06-10: this file IS in the build — imported by `ArkLib.lean`.) -/

open scoped NNReal ENNReal
open MutualCorrAgreement ProbabilityTheory ReedSolomon Generator

namespace MCAJohnsonSmallField

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem mca_johnson_bound_CONJECTURE_smallField
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ]
    (parℓ_type : Type) [Fintype parℓ_type] (exp : parℓ_type ↪ ℕ)
    (hr0 : 0 < (RSGenerator.genRSC parℓ_type φ m exp).rate)
    (hr1 : (RSGenerator.genRSC parℓ_type φ m exp).rate ≤ 1)
    (hcard2 : 2 ≤ Fintype.card parℓ_type)
    (hF : (Fintype.card F : ℝ)
        ≤ (((Fintype.card parℓ_type : ℝ) - 1) * (2 : ℝ) ^ (2 * m)) * 10 ^ 7) :
    mca_johnson_bound_CONJECTURE α φ m parℓ_type exp := by
  classical
  unfold mca_johnson_bound_CONJECTURE
  rintro Gen f δ ⟨hδ0, hδ1⟩
  refine le_trans (PMF.coe_le_one _ _) ?_
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  set ρ := Gen.rate with hρ
  have hr0' : 0 < ρ := hr0
  have hr1' : ρ ≤ 1 := hr1
  set sρ : ℝ := Real.sqrt ρ with hsρ
  set mv : ℝ := min (1 - sρ - (δ : ℝ)) (sρ / 20) with hmv
  have hsρpos : 0 < sρ := Real.sqrt_pos.mpr hr0'
  have hsρle1 : sρ ≤ 1 := by
    rw [hsρ, show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hr1'
  have hmv_pos : 0 < mv := by
    rw [hmv]; apply lt_min
    · have : (δ : ℝ) < 1 - sρ := by rw [hsρ]; exact_mod_cast hδ1
      linarith
    · positivity
  have hmv_le : mv ≤ sρ / 20 := by rw [hmv]; exact min_le_right _ _
  have h2mv : 2 * mv ≤ 1 / 10 := by
    have hsρ20 : sρ / 20 ≤ 1 / 20 := by linarith
    linarith [hmv_le]
  have h2mv_pos : 0 < 2 * mv := by positivity
  have hpow7 : (2 * mv) ^ 7 ≤ (1 / 10 : ℝ) ^ 7 := by gcongr
  have hpow7_pos : 0 < (2 * mv) ^ 7 := by positivity
  set NUM : ℝ := ((Fintype.card parℓ_type : ℝ) - 1) * (2 : ℝ) ^ (2 * m) with hNUM
  have hNUM_pos : 0 < NUM := by
    rw [hNUM]
    have : (1 : ℝ) ≤ (Fintype.card parℓ_type : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (Fintype.card parℓ_type : ℝ) := by exact_mod_cast hcard2
      linarith
    positivity
  have hcardF_pos : 0 < (Fintype.card F : ℝ) := by
    have : 0 < Fintype.card F := Fintype.card_pos; exact_mod_cast this
  have hden_le : (Fintype.card F : ℝ) * (2 * mv) ^ 7 ≤ NUM := by
    calc (Fintype.card F : ℝ) * (2 * mv) ^ 7
        ≤ (Fintype.card F : ℝ) * (1 / 10 : ℝ) ^ 7 := by gcongr
      _ = (Fintype.card F : ℝ) / 10 ^ 7 := by ring
      _ ≤ NUM := by rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10 ^ 7)]; exact hF
  have hden_pos : 0 < (Fintype.card F : ℝ) * (2 * mv) ^ 7 := by positivity
  rw [le_div_iff₀ hden_pos, one_mul]
  exact hden_le

end MCAJohnsonSmallField


/-! ## Axiom audit -/
#print axioms MCAJohnsonSmallField.mca_johnson_bound_CONJECTURE_smallField
