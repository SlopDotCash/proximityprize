/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26PolyFieldCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZTZBetaThreeLadderExtension
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZTZBetaThreeHighLadderExtension
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZTZBetaFiveLadderExtension

/-!
# Unconditional [KKH26] δ* ceilings at β = 3 (`n = 512 … 16384`) and β = 5 (`n = 16 … 64`) (#466/#334)

Sibling of `Frontier/_ZTZBetaFourCeilingWiring.lean` (which wires the quartic rungs): this file
consumes the just-landed **cubic** supply rungs `tzPrimeSupply_{512,1024,2048,4096}_three`
(`Frontier/_ZTZBetaThreeLadderExtension.lean`) and `tzPrimeSupply_{8192,16384}_three`
(`Frontier/_ZTZBetaThreeHighLadderExtension.lean`), and the **quintic** rungs
`tzPrimeSupply_{16,32,64}_five` (`Frontier/_ZTZBetaFiveLadderExtension.lean`) — all
`TZPrimeSupply n β 12`, twelve Lucas-certified primes each — through
`kkh26_mcaDeltaStar_le_of_TZ`.  Because the rungs are **proven** (not named hypotheses), each
resulting ceiling is an **unconditional, axiom-clean theorem**:

> **`kkh26_mcaDeltaStar_le_concrete_n{512,…,16384}_beta3`**, **`…_n{16,32,64}_beta5`** — for each
> `n` there is a prime `p ≡ 1 (mod n)` with `n^β ≤ p ≤ 2·n^β` and a smooth domain
> `⟨g⟩ ⊆ F_p^×` of order `n` such that `mcaDeltaStar(evalCode g n 0, ε*) ≤ 1 − 2/2² = 1/2`
> for every `ε* < 4/p`.

Together with the β = 4 sibling this realizes the [KKH26] polynomial-field-size ceiling across
**three field-size scalings** `p ≈ n³, n⁴, n⁵` (field sizes `2²⁰ … 2⁴³`), all strictly below
capacity.

**Parameters.**  Each `n` is written `n = 2²·m` (`μ = 2`, `r = 2`, `m = n/4`): then
`r ≤ 2^(μ−1) = 2` ✓, the ceiling is `1 − r/2^μ = 1/2`, the target-error window is
`2^r·(2^{μ−1}).choose r / p = 4/p`, and the code degree bound is `(r−2)·m = 0`.  The bad-prime
budget closes as in the template: `|collisionPairs 2 2| = 12` and
`log 16 / log(n^β) = (4 log 2)/(β·log₂n·log 2)`, so the budget is
`48/(β·log₂n) ≤ 48/20 = 2.4 < 12` — strictly under the supply at every rung
(β = 3: denominators 27, 30, 33, 36, 39, 42; β = 5: denominators 20, 25, 30).
Axiom-clean (`propext, Classical.choice, Quot.sound`), no `native_decide`, no `axiom`,
no `sorry`.

## References
* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782 (Lemma 2, Theorem 1).  Issues #334 / #466.
* [TZ24] J. Thorner, A. Zaman, *Refinements to the prime number theorem in arithmetic
  progressions*, Cor 3.1.
-/

open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.KKH26

/-! ### β = 3 rungs: `n = 512, 1024, 2048, 4096, 8192, 16384` -/

/-- **Unconditional [KKH26] δ* ceiling at order 512, β = 3.**  End-to-end via
`tzPrimeSupply_512_three` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n512_beta3 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 512] ∧
      ((512 : ℕ) : ℝ) ^ (3 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((512 : ℕ) : ℝ) ^ (3 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 512 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 512 ((2 - 2) * 128)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (512 : ℕ) := ⟨by norm_num⟩
  have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaThreeLadder.tzPrimeSupply_512_three
      (μ := 2) (m := 128) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h3, Real.rpow_natCast]; norm_num) (by rw [h3, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(27 log2) = 48/27 ≈ 1.78 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((512 : ℕ) : ℝ) ^ (3 : ℝ)) = 27 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((512 : ℕ) : ℝ) = (2 : ℝ) ^ (9 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-- **Unconditional [KKH26] δ* ceiling at order 1024, β = 3.**  End-to-end via
`tzPrimeSupply_1024_three` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n1024_beta3 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 1024] ∧
      ((1024 : ℕ) : ℝ) ^ (3 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((1024 : ℕ) : ℝ) ^ (3 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 1024 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 1024 ((2 - 2) * 256)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (1024 : ℕ) := ⟨by norm_num⟩
  have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaThreeLadder.tzPrimeSupply_1024_three
      (μ := 2) (m := 256) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h3, Real.rpow_natCast]; norm_num) (by rw [h3, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(30 log2) = 48/30 = 1.6 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((1024 : ℕ) : ℝ) ^ (3 : ℝ)) = 30 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((1024 : ℕ) : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-- **Unconditional [KKH26] δ* ceiling at order 2048, β = 3.**  End-to-end via
`tzPrimeSupply_2048_three` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n2048_beta3 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 2048] ∧
      ((2048 : ℕ) : ℝ) ^ (3 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((2048 : ℕ) : ℝ) ^ (3 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 2048 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 2048 ((2 - 2) * 512)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (2048 : ℕ) := ⟨by norm_num⟩
  have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaThreeLadder.tzPrimeSupply_2048_three
      (μ := 2) (m := 512) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h3, Real.rpow_natCast]; norm_num) (by rw [h3, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(33 log2) = 48/33 ≈ 1.45 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((2048 : ℕ) : ℝ) ^ (3 : ℝ)) = 33 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((2048 : ℕ) : ℝ) = (2 : ℝ) ^ (11 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-- **Unconditional [KKH26] δ* ceiling at order 4096, β = 3.**  End-to-end via
`tzPrimeSupply_4096_three` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n4096_beta3 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 4096] ∧
      ((4096 : ℕ) : ℝ) ^ (3 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((4096 : ℕ) : ℝ) ^ (3 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 4096 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 4096 ((2 - 2) * 1024)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (4096 : ℕ) := ⟨by norm_num⟩
  have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaThreeLadder.tzPrimeSupply_4096_three
      (μ := 2) (m := 1024) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h3, Real.rpow_natCast]; norm_num) (by rw [h3, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(36 log2) = 48/36 ≈ 1.33 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((4096 : ℕ) : ℝ) ^ (3 : ℝ)) = 36 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((4096 : ℕ) : ℝ) = (2 : ℝ) ^ (12 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-- **Unconditional [KKH26] δ* ceiling at order 8192, β = 3.**  End-to-end via
`tzPrimeSupply_8192_three` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n8192_beta3 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 8192] ∧
      ((8192 : ℕ) : ℝ) ^ (3 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((8192 : ℕ) : ℝ) ^ (3 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 8192 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 8192 ((2 - 2) * 2048)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (8192 : ℕ) := ⟨by norm_num⟩
  have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaThreeHighLadder.tzPrimeSupply_8192_three
      (μ := 2) (m := 2048) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h3, Real.rpow_natCast]; norm_num) (by rw [h3, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(39 log2) = 48/39 ≈ 1.23 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((8192 : ℕ) : ℝ) ^ (3 : ℝ)) = 39 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((8192 : ℕ) : ℝ) = (2 : ℝ) ^ (13 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-- **Unconditional [KKH26] δ* ceiling at order 16384, β = 3.**  End-to-end via
`tzPrimeSupply_16384_three` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n16384_beta3 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 16384] ∧
      ((16384 : ℕ) : ℝ) ^ (3 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((16384 : ℕ) : ℝ) ^ (3 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 16384 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 16384 ((2 - 2) * 4096)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (16384 : ℕ) := ⟨by norm_num⟩
  have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaThreeHighLadder.tzPrimeSupply_16384_three
      (μ := 2) (m := 4096) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h3, Real.rpow_natCast]; norm_num) (by rw [h3, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(42 log2) = 48/42 ≈ 1.14 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((16384 : ℕ) : ℝ) ^ (3 : ℝ)) = 42 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((16384 : ℕ) : ℝ) = (2 : ℝ) ^ (14 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-! ### β = 5 rungs: `n = 16, 32, 64` -/

/-- **Unconditional [KKH26] δ* ceiling at order 16, β = 5.**  End-to-end via
`tzPrimeSupply_16_five` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n16_beta5 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 16] ∧
      ((16 : ℕ) : ℝ) ^ (5 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((16 : ℕ) : ℝ) ^ (5 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 16 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 16 ((2 - 2) * 4)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  have h5 : (5 : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaFiveLadder.tzPrimeSupply_16_five
      (μ := 2) (m := 4) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h5, Real.rpow_natCast]; norm_num) (by rw [h5, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(20 log2) = 48/20 = 2.4 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((16 : ℕ) : ℝ) ^ (5 : ℝ)) = 20 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((16 : ℕ) : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-- **Unconditional [KKH26] δ* ceiling at order 32, β = 5.**  End-to-end via
`tzPrimeSupply_32_five` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n32_beta5 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 32] ∧
      ((32 : ℕ) : ℝ) ^ (5 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((32 : ℕ) : ℝ) ^ (5 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 32 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 32 ((2 - 2) * 8)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (32 : ℕ) := ⟨by norm_num⟩
  have h5 : (5 : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaFiveLadder.tzPrimeSupply_32_five
      (μ := 2) (m := 8) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h5, Real.rpow_natCast]; norm_num) (by rw [h5, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(25 log2) = 48/25 = 1.92 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((32 : ℕ) : ℝ) ^ (5 : ℝ)) = 25 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((32 : ℕ) : ℝ) = (2 : ℝ) ^ (5 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-- **Unconditional [KKH26] δ* ceiling at order 64, β = 5.**  End-to-end via
`tzPrimeSupply_64_five` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n64_beta5 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 64] ∧
      ((64 : ℕ) : ℝ) ^ (5 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((64 : ℕ) : ℝ) ^ (5 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 64 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 64 ((2 - 2) * 16)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (64 : ℕ) := ⟨by norm_num⟩
  have h5 : (5 : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaFiveLadder.tzPrimeSupply_64_five
      (μ := 2) (m := 16) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h5, Real.rpow_natCast]; norm_num) (by rw [h5, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(30 log2) = 48/30 = 1.6 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((64 : ℕ) : ℝ) ^ (5 : ℝ)) = 30 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((64 : ℕ) : ℝ) = (2 : ℝ) ^ (6 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n512_beta3
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n1024_beta3
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n2048_beta3
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n4096_beta3
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n8192_beta3
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n16384_beta3
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n16_beta5
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n32_beta5
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n64_beta5
