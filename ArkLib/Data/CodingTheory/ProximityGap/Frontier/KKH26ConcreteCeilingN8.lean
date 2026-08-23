/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26PolyFieldCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ThornerZamanInstance

/-!
# A concrete [KKH26] δ* ceiling at domain order 8, β = 3 (#334/B3)

`KKH26ConcreteCeiling.lean` discharges the [KKH26] ceiling end-to-end at the smallest smooth domain
(order `4`, `β = 4`).  This file demonstrates the pipeline **scales to a larger domain and a
different exponent**: order `8 = 2²·2` at `β = 3` — the faithful unconditional [TZ24] regime `β > 12/5`.

> **`kkh26_mcaDeltaStar_le_concrete_n8`** — there is a prime `p ≡ 1 (mod 8)` with `8³ ≤ p ≤ 2·8³`
> and a smooth domain `⟨g⟩ ⊆ F_p^×` of order `8` such that
> `mcaDeltaStar(evalCode g 8 0, ε*) ≤ 1 − 2/2² = 1/2` for every `ε* < 4/p`.

It reuses the concrete supply `tzPrimeSupply_8_three` (`TZPrimeSupply 8 3 8`, ten — here eight —
explicit primes `≡ 1 (mod 8)` in `[8³, 2·8³]`) and feeds it through the conditional consumer
`kkh26_mcaDeltaStar_le_of_TZ`.  The bad-prime budget closes: with `μ = 2, r = 2`,
`|collisionPairs 2 2| = 12`, and `12 · log(16)/log(8³) = 12·(4/9) = 48/9 ≈ 5.33 < 8` — strictly under
the supply.  Axiom-clean (`propext, Classical.choice, Quot.sound`), no `native_decide`, no `axiom`.
-/

open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.KKH26

/-- **Concrete [KKH26] δ* ceiling at order 8, β = 3.**  A prime `p ≡ 1 (mod 8)` with `8³ ≤ p ≤ 2·8³`
and an order-8 smooth domain `⟨g⟩` pin `mcaDeltaStar(evalCode g 8 0, ε*) ≤ 1/2` for `ε* < 4/p`.
End-to-end discharge via `tzPrimeSupply_8_three` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n8 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 8] ∧
      ((8 : ℕ) : ℝ) ^ (3 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((8 : ℕ) : ℝ) ^ (3 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 8 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 8 ((2 - 2) * 2)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ tzPrimeSupply_8_three (μ := 2) (m := 2) (r := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [h3, Real.rpow_natCast]; norm_num) (by rw [h3, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · log(16)/log(8³) = 48/9 ≈ 5.33 < 8
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have h512 : Real.log (((8 : ℕ) : ℝ) ^ (3 : ℝ)) = 9 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((8 : ℕ) : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, h512, mul_div_mul_right _ _ hlog2]
  norm_num

end ArkLib.ProximityGap.KKH26

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n8
