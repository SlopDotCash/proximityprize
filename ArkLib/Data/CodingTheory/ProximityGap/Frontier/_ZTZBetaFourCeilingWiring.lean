/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26PolyFieldCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZTZBetaFourLadderExtension

/-!
# Unconditional [KKH26] δ* ceilings at `n ∈ {128, 256, 512, 1024}`, β = 4 (#466/#334)

`Frontier/KKH26ConcreteCeilingN8.lean` discharges the [KKH26] `δ*` ceiling end-to-end at the
smallest smooth domain (order `8`, `β = 3`).  This file **scales that end-to-end pin to the
polynomial-field-size regime `n ∈ {128, 256, 512, 1024}` at `β = 4`**, consuming the just-landed
quartic Thorner–Zaman supply rungs `tzPrimeSupply_{128,256,512,1024}_four`
(`Frontier/_ZTZBetaFourLadderExtension.lean`, `TZPrimeSupply n (4:ℝ) 12`, twelve Lucas-certified
primes each).  Because those rungs are **proven** (not named hypotheses), the resulting ceilings
are **unconditional, axiom-clean theorems**.

> **`kkh26_mcaDeltaStar_le_concrete_n{128,256,512,1024}`** — for each `n` there is a prime
> `p ≡ 1 (mod n)` with `n⁴ ≤ p ≤ 2·n⁴` and a smooth domain `⟨g⟩ ⊆ F_p^×` of order `n` such that
> `mcaDeltaStar(evalCode g n 0, ε*) ≤ 1 − 2/2² = 1/2` for every `ε* < 4/p`.

**Parameters.**  Each `n` is written `n = 2²·m` (`μ = 2`, `r = 2`, `m = n/4`): then
`r ≤ 2^(μ−1) = 2` ✓, the ceiling is `1 − r/2^μ = 1/2`, the target-error window is
`2^r·(2^{μ−1}).choose r / p = 4/p`, and the code degree bound is `(r−2)·m = 0`.  The bad-prime
budget closes the same way as the `n = 8` template: `|collisionPairs 2 2| = 12` and
`log((2²)^(2^1))/log(n⁴) = log 16 / log(n⁴) = (4 log 2)/(4·log₂n·log 2)`, so the budget is
`12·(4 log 2)/(4·log₂n·log 2) = 12/log₂n ∈ {12/7, 12/8, 12/9, 12/10} < 12` — strictly under the
supply for every rung.  Axiom-clean (`propext, Classical.choice, Quot.sound`), no `native_decide`,
no `axiom`, no `sorry`.

## References
* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782 (Lemma 2, Theorem 1).  Issues #334 / #466.
* [TZ24] J. Thorner, A. Zaman, *Refinements to the prime number theorem in arithmetic
  progressions*, Cor 3.1.
-/

open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.KKH26

/-! ### `n = 128 = 2²·32`, β = 4 -/

/-- **Unconditional [KKH26] δ* ceiling at order 128, β = 4.**  A prime `p ≡ 1 (mod 128)` with
`128⁴ ≤ p ≤ 2·128⁴` and an order-128 smooth domain `⟨g⟩` pin
`mcaDeltaStar(evalCode g 128 0, ε*) ≤ 1/2` for `ε* < 4/p`.  End-to-end via
`tzPrimeSupply_128_four` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n128 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 128] ∧
      ((128 : ℕ) : ℝ) ^ (4 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((128 : ℕ) : ℝ) ^ (4 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 128 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 128 ((2 - 2) * 32)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (128 : ℕ) := ⟨by norm_num⟩
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaFourLadder.tzPrimeSupply_128_four
      (μ := 2) (m := 32) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h4, Real.rpow_natCast]; norm_num) (by rw [h4, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · log(16)/log(128⁴) = 12 · (4 log2)/(28 log2) = 12/7 ≈ 1.71 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((128 : ℕ) : ℝ) ^ (4 : ℝ)) = 28 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((128 : ℕ) : ℝ) = (2 : ℝ) ^ (7 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-! ### `n = 256 = 2²·64`, β = 4 -/

/-- **Unconditional [KKH26] δ* ceiling at order 256, β = 4.**  A prime `p ≡ 1 (mod 256)` with
`256⁴ ≤ p ≤ 2·256⁴` and an order-256 smooth domain `⟨g⟩` pin
`mcaDeltaStar(evalCode g 256 0, ε*) ≤ 1/2` for `ε* < 4/p`.  End-to-end via
`tzPrimeSupply_256_four` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n256 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 256] ∧
      ((256 : ℕ) : ℝ) ^ (4 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((256 : ℕ) : ℝ) ^ (4 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 256 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 256 ((2 - 2) * 64)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (256 : ℕ) := ⟨by norm_num⟩
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaFourLadder.tzPrimeSupply_256_four
      (μ := 2) (m := 64) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h4, Real.rpow_natCast]; norm_num) (by rw [h4, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(32 log2) = 12/8 = 1.5 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((256 : ℕ) : ℝ) ^ (4 : ℝ)) = 32 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((256 : ℕ) : ℝ) = (2 : ℝ) ^ (8 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-! ### `n = 512 = 2²·128`, β = 4 -/

/-- **Unconditional [KKH26] δ* ceiling at order 512, β = 4.**  A prime `p ≡ 1 (mod 512)` with
`512⁴ ≤ p ≤ 2·512⁴` and an order-512 smooth domain `⟨g⟩` pin
`mcaDeltaStar(evalCode g 512 0, ε*) ≤ 1/2` for `ε* < 4/p`.  End-to-end via
`tzPrimeSupply_512_four` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n512 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 512] ∧
      ((512 : ℕ) : ℝ) ^ (4 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((512 : ℕ) : ℝ) ^ (4 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 512 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 512 ((2 - 2) * 128)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (512 : ℕ) := ⟨by norm_num⟩
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaFourLadder.tzPrimeSupply_512_four
      (μ := 2) (m := 128) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h4, Real.rpow_natCast]; norm_num) (by rw [h4, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(36 log2) = 12/9 ≈ 1.33 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((512 : ℕ) : ℝ) ^ (4 : ℝ)) = 36 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((512 : ℕ) : ℝ) = (2 : ℝ) ^ (9 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-! ### `n = 1024 = 2²·256`, β = 4 -/

/-- **Unconditional [KKH26] δ* ceiling at order 1024, β = 4.**  A prime `p ≡ 1 (mod 1024)` with
`1024⁴ ≤ p ≤ 2·1024⁴` and an order-1024 smooth domain `⟨g⟩` pin
`mcaDeltaStar(evalCode g 1024 0, ε*) ≤ 1/2` for `ε* < 4/p`.  End-to-end via
`tzPrimeSupply_1024_four` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n1024 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 1024] ∧
      ((1024 : ℕ) : ℝ) ^ (4 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((1024 : ℕ) : ℝ) ^ (4 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 1024 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 1024 ((2 - 2) * 256)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (1024 : ℕ) := ⟨by norm_num⟩
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaFourLadder.tzPrimeSupply_1024_four
      (μ := 2) (m := 256) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h4, Real.rpow_natCast]; norm_num) (by rw [h4, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(40 log2) = 12/10 = 1.2 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((1024 : ℕ) : ℝ) ^ (4 : ℝ)) = 40 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((1024 : ℕ) : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n128
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n256
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n512
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n1024
