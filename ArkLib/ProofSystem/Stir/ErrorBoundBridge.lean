/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.ProofSystem.Stir.ProximityBound

/-!
# STIR proximity-error ↔ BCIKS error-bound threshold bridge

The STIR low-degree test states its proximity gap against `STIR.proximityError`, while the
in-tree BCIKS20 keystone (`ProximityGap.errorBound`, consumed by
`correlatedAgreement_affine_curves`) uses `errorBound`. This file proves the noted
`proximityError ↔ (m−1)·errorBound` bridge (referenced as a residual requirement in
`BCIKS20/Curves/UniqueDecoding.lean`), letting a STIR-form proximity-gap statement consume the
keystone's native threshold.
-/

open NNReal ReedSolomon

namespace STIR

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Threshold bridge** (the noted `proximityError ↔ (m−1)·errorBound` requirement):
`proximityError` dominates `(m−1)·errorBound`. Equal in the Johnson branch; in the
unique-decoding branch `deg/ρ = deg·|ι|/min(deg,|ι|) ≥ |ι|` provides the gap. -/
theorem mul_errorBound_le_proximityError
    {deg m : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] :
    ((m : ℝ≥0) - 1) * ProximityGap.errorBound δ deg domain
      ≤ proximityError F deg (LinearCode.rate (ReedSolomon.code domain deg)) δ m := by
  classical
  set ρ : ℝ≥0 := ((LinearCode.rate (ReedSolomon.code domain deg) : ℚ≥0) : ℝ≥0) with hρ
  have hdeg : 1 ≤ deg := Nat.one_le_iff_ne_zero.mpr (NeZero.ne deg)
  have hrate : ρ = (min deg (Fintype.card ι) : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
    rw [hρ, ReedSolomon.rateOfLinearCode_eq_min_div]
    push_cast
    ring
  have hcardι : 0 < Fintype.card ι := Fintype.card_pos
  rw [proximityError, ProximityGap.errorBound]
  simp only [← hρ, Set.mem_Icc, Set.mem_Ioo, zero_le, true_and]
  have hρr : (ρ : ℝ) = (min deg (Fintype.card ι) : ℝ) / (Fintype.card ι : ℝ) := by
    rw [hrate]; push_cast; ring
  have hmin_pos : (0 : ℝ) < (min deg (Fintype.card ι) : ℝ) := by
    have : 0 < min deg (Fintype.card ι) := lt_min hdeg hcardι
    exact_mod_cast this
  have hcardι' : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hcardι
  have hmin_le : (min deg (Fintype.card ι) : ℝ) ≤ (deg : ℝ) := by exact_mod_cast min_le_left _ _
  by_cases h1 : δ ≤ (1 - ρ) / 2
  · simp only [h1, if_true]
    -- factor (m-1) at the ℝ≥0 level to avoid coercion of ℕ subtraction
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (zero_le _)
    -- goal (ℝ≥0): |ι|/|F| ≤ deg/(ρ*|F|)
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [hρr]
    rcases Nat.eq_zero_or_pos (Fintype.card F) with hF | hF
    · simp [hF]
    · have hF' : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hF
      rw [div_le_div_iff₀ hF' (mul_pos (div_pos hmin_pos hcardι') hF')]
      have hcancel : (Fintype.card ι : ℝ)
          * (min (deg : ℝ) (Fintype.card ι) / (Fintype.card ι : ℝ) * (Fintype.card F : ℝ))
          = min (deg : ℝ) (Fintype.card ι) * (Fintype.card F : ℝ) := by
        field_simp
      rw [hcancel]
      exact mul_le_mul_of_nonneg_right hmin_le hF'.le
  · simp only [h1, if_false]
    by_cases h2 : δ < 1 - ρ.sqrt
    · have h1' : (1 - ρ) / 2 < δ := not_le.mp h1
      simp only [h2, h1', if_true, and_true]
      apply le_of_eq
      rw [mul_div_assoc]
      congr 1
      rw [← NNReal.coe_inj]
      erw [NNReal.coe_mk]
      push_cast
      ring
    · simp [h2]

end STIR
