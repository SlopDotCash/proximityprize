/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWindowInteriorFamily

/-!
# `johnsonTightness_REFUTED` (#357): δ* = 1 − √ρ is NOT a law of the challenge family

**Candidate hypothesis under test (Johnson tightness):** for every smooth-domain
Reed–Solomon code in the [ABF26] grand-MCA-challenge family (rate ρ ∈ {1/2,…,1/16},
`k ≤ 2⁴⁰`, `|F| < 2²⁵⁶`, ε* = 2⁻¹²⁸), the MCA threshold is exactly the Johnson radius:
`mcaDeltaStar C 2⁻¹²⁸ = 1 − √ρ`; equivalently, a bad witness with `ε_mca > 2⁻¹²⁸`
exists at **every** δ > 1 − √ρ.

**Verdict: REFUTED** — by a genuine member of the challenge family on the
*above-Johnson* side. For `RS[F, domain, 4]` on an 8-point domain (any domain, in
particular the smooth domain μ₈ ⊆ F* for any prime `q ≡ 1 mod 8`; rate ρ = 1/2)
over any field with `q ≥ 70·2¹²⁸` (≈ 2¹³⁴·¹, far below the 2²⁵⁶ cap):

  `δ*(RS[F, 8 pts, 4], 2⁻¹²⁸) ≥ 1/2 > 1 − √(1/2) ≈ 0.2929… = Johnson`.

So the radius `δ = 1/2` strictly above Johnson is a GOOD radius (`ε_mca ≤ 2⁻¹²⁸`,
`epsMCA_rs84_half_good`): **no** bad witness construction exists there, refuting the
"bad witness at every δ > 1 − √ρ" half of the hypothesis at this family member, and
`mcaDeltaStar_rs84_ne_johnson` refutes the exact-value half.

Engine: the unconditional LYM/antichain reach `le_mcaDeltaStar_lym_family`
(`MCAWindowInteriorFamily.lean`) at layer `t = 4` (`n = 8 ≤ 2t`), with
`C(8,4) = 70 ≤ ε*·q`. The complementary small-field corner (`q < 2·2¹²⁸`:
`δ* < 1/n` ≪ Johnson, from the spike floor `epsMCA_generalJ_ge` +
`mcaDeltaStar_le_of_bad`) kills the law from below; this file is the above-Johnson
kill. Neither corner touches the production core (`n ≥ 2²⁰`, `q ≥ n·2¹²⁸·ω(1)`),
where Johnson-vs-above remains the open core (`candidate_exact_delta_star_OPEN`).

Axiom-clean; no `sorry`.
-/

set_option autoImplicit false

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger ProximityGap.MCAWindowInteriorFamily

namespace ProximityGap.JohnsonTightnessRefuted

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The Johnson radius of a rate-1/2 code is strictly below `1/2`:
`1 − √(1/2) < 1/2` (since `√(1/2) > √(1/4) = 1/2`). -/
theorem johnson_half_rate_lt_half : 1 - Real.sqrt (1 / 2) < (1 / 2 : ℝ) := by
  have h14 : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1 / 2)
  rw [h14] at h
  linarith

/-- `1 − 4/8 = 1/2` in `ℝ≥0` (truncated subtraction discharged via coercion). -/
private theorem one_sub_four_div_eight : (1 : ℝ≥0) - (4 : ℝ≥0) / (8 : ℝ≥0) = 1 / 2 := by
  rw [← NNReal.coe_inj, NNReal.coe_sub (by norm_num)]
  push_cast
  norm_num

/-- **The above-Johnson good radius.** For `RS[F, domain, 4]` on an 8-point domain with
`70·2¹²⁸ ≤ q`: `δ* ≥ 1/2` at the prize accuracy `ε* = 2⁻¹²⁸`. Instance of the
unconditional LYM family floor at layer `t = 4`. -/
theorem mcaDeltaStar_rs84_ge_half (domain : Fin 8 ↪ F)
    (hq : (70 : ℝ≥0∞) * 2 ^ 128 ≤ (Fintype.card F : ℝ≥0∞)) :
    (1 / 2 : ℝ≥0) ≤ mcaDeltaStar (F := F) (A := F)
      (ReedSolomon.code domain 4 : Set (Fin 8 → F)) ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  have h2ne0 : ((2 : ℝ≥0∞) ^ 128) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2neT : ((2 : ℝ≥0∞) ^ 128) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hF0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hε : ((Fintype.card (Fin 8)).choose 4 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
    rw [Fintype.card_fin, show Nat.choose 8 4 = 70 from by decide]
    rw [ENNReal.div_le_iff hF0 (ENNReal.natCast_ne_top _)]
    calc ((70 : ℕ) : ℝ≥0∞) = (70 : ℝ≥0∞) * 2 ^ 128 * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel h2ne0 h2neT, mul_one]
          norm_num
      _ ≤ (Fintype.card F : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by gcongr
      _ = ((2 : ℝ≥0∞) ^ 128)⁻¹ * (Fintype.card F : ℝ≥0∞) := mul_comm _ _
  have h := le_mcaDeltaStar_lym_family (F := F) (A := F)
    (ReedSolomon.code domain 4) (t := 4)
    (by simp [Fintype.card_fin]) (by simp [Fintype.card_fin]) hε
  rw [Fintype.card_fin] at h
  calc (1 / 2 : ℝ≥0) = 1 - (4 : ℝ≥0) / (8 : ℝ≥0) := one_sub_four_div_eight.symm
    _ ≤ _ := by exact_mod_cast h

/-- **No bad witness at `δ = 1/2` (strictly above Johnson).** The MCA error of
`RS[F, 8 pts, 4]` at radius `1/2` is at most `2⁻¹²⁸` whenever `70·2¹²⁸ ≤ q`:
the "bad witness construction at every δ > 1 − √ρ" claim fails at this code. -/
theorem epsMCA_rs84_half_good (domain : Fin 8 ↪ F)
    (hq : (70 : ℝ≥0∞) * 2 ^ 128 ≤ (Fintype.card F : ℝ≥0∞)) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain 4 : Set (Fin 8 → F)) (1 / 2 : ℝ≥0)
      ≤ ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  have h2ne0 : ((2 : ℝ≥0∞) ^ 128) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2neT : ((2 : ℝ≥0∞) ^ 128) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hF0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hceil : ⌈((1 : ℝ≥0) - (1 / 2 : ℝ≥0)) * ((Fintype.card (Fin 8)) : ℝ≥0)⌉₊ = 4 := by
    rw [Fintype.card_fin]
    rw [show (1 : ℝ≥0) - (1 / 2 : ℝ≥0) = 1 / 2 from by
      rw [← NNReal.coe_inj, NNReal.coe_sub (by norm_num)]; norm_num]
    rw [show (1 / 2 : ℝ≥0) * ((8 : ℕ) : ℝ≥0) = ((4 : ℕ) : ℝ≥0) from by push_cast; ring]
    exact Nat.ceil_natCast 4
  have hbound := ProximityGap.MCAAntichainLYM.epsMCA_le_choose_ceil_div
    (F := F) (A := F) (ReedSolomon.code domain 4) (1 / 2 : ℝ≥0)
    (by rw [hceil, Fintype.card_fin])
  rw [hceil, Fintype.card_fin, show Nat.choose 8 4 = 70 from by decide] at hbound
  refine le_trans hbound ?_
  rw [ENNReal.div_le_iff hF0 (ENNReal.natCast_ne_top _)]
  calc ((70 : ℕ) : ℝ≥0∞) = (70 : ℝ≥0∞) * 2 ^ 128 * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel h2ne0 h2neT, mul_one]
        norm_num
    _ ≤ (Fintype.card F : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by gcongr
    _ = ((2 : ℝ≥0∞) ^ 128)⁻¹ * (Fintype.card F : ℝ≥0∞) := mul_comm _ _

/-- **Johnson tightness REFUTED (exact-value half).** At the witness code,
`δ* ≥ 1/2` while the rate-1/2 Johnson radius is `1 − √(1/2) < 1/2`: the threshold is
NOT the Johnson radius — `(1 − √ρ : ℝ) < δ*`. -/
theorem mcaDeltaStar_rs84_ne_johnson (domain : Fin 8 ↪ F)
    (hq : (70 : ℝ≥0∞) * 2 ^ 128 ≤ (Fintype.card F : ℝ≥0∞)) :
    1 - Real.sqrt (1 / 2) <
      (mcaDeltaStar (F := F) (A := F)
        (ReedSolomon.code domain 4 : Set (Fin 8 → F)) ((2 : ℝ≥0∞) ^ 128)⁻¹ : ℝ) := by
  have h := mcaDeltaStar_rs84_ge_half domain hq
  have hcoe : (1 / 2 : ℝ) ≤
      (mcaDeltaStar (F := F) (A := F)
        (ReedSolomon.code domain 4 : Set (Fin 8 → F)) ((2 : ℝ≥0∞) ^ 128)⁻¹ : ℝ) := by
    exact_mod_cast h
  linarith [johnson_half_rate_lt_half]

end ProximityGap.JohnsonTightnessRefuted

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.JohnsonTightnessRefuted.johnson_half_rate_lt_half
#print axioms ProximityGap.JohnsonTightnessRefuted.mcaDeltaStar_rs84_ge_half
#print axioms ProximityGap.JohnsonTightnessRefuted.epsMCA_rs84_half_good
#print axioms ProximityGap.JohnsonTightnessRefuted.mcaDeltaStar_rs84_ne_johnson
