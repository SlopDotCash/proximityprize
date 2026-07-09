/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PrizeEntropyDeltaStar
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DimOnePin

/-!
# The proposed entropy pin is refuted, even after correcting the code rate

`PrizePinConjecture g k epsilonStar` feeds `k / n` to the entropy formula while using
`evalCode g n k`.  In this code API, `k` is the polynomial degree bound, so the code has
dimension `k + 1`.  The mismatch is already decisive at degree zero.

For the eight-point constant code over `F_12289`, the unconditional KKH26 dimension-one
theorem proves that the operational threshold at budget `14/12289` is `3/4`.  The old
entropy expression sees the supplied rate as `0/8`; binary entropy vanishes at zero, so it
returns `1`, independently of the budget.  Hence this concrete instance of
`PrizePinConjecture` is false.

Correcting the rate does not rescue the generic formula.  An exact logarithmic certificate
below proves

`3/4 < prizeDeltaStar (1/8) 14`.

The left side is the known exact threshold of the same code, while `1/8` and `14` are its
actual rate and list budget.  Thus the actual-rate equality is also false at this finite
instance.  This does not determine the four production prize instances or refute a suitably
qualified asymptotic statement.
-/

set_option autoImplicit false

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ProximityGap.PrizeEntropy
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.KKH26DimOne

namespace ProximityGap.PrizeEntropy

local instance fact_prime_12289_refutation : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- At the zero rate supplied by the stale degree parameter, the entropy candidate is `1`. -/
theorem prizeDeltaStar_zero_rate (B : ℝ) : prizeDeltaStar 0 B = 1 := by
  simp [prizeDeltaStar]

/-! ## The actual-rate candidate is also false -/

/-- Exact expansion of Mathlib's natural-log binary entropy at rate `1/8`. -/
theorem binEntropy_one_eighth_exact :
    Real.binEntropy (1 / 8 : ℝ) =
      (3 / 8 : ℝ) * Real.log 2 + (7 / 8 : ℝ) * Real.log ((8 : ℝ) / 7) := by
  rw [Real.binEntropy]
  norm_num [Real.log_inv]
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  ring

/-- A rational upper certificate for the entropy at rate `1/8`. -/
theorem binEntropy_one_eighth_lt_two_fifths :
    Real.binEntropy (1 / 8 : ℝ) < 2 / 5 := by
  have hlog2 : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hlog87 : Real.log ((8 : ℝ) / 7) < (1 / 7 : ℝ) := by
    have h := Real.log_lt_sub_one_of_pos
      (x := (8 : ℝ) / 7) (by positivity) (by norm_num)
    norm_num at h ⊢
    exact h
  rw [binEntropy_one_eighth_exact]
  nlinarith

/-- The base-two logarithm of the concrete list budget `14` is greater than `7/2`.
The certificate is the exact integer inequality `2^7 < 14^2`. -/
theorem seven_halves_lt_logb_two_fourteen :
    (7 / 2 : ℝ) < Real.logb 2 14 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpowers : Real.log ((2 : ℝ) ^ 7) < Real.log ((14 : ℝ) ^ 2) := by
    apply (Real.log_lt_log_iff (by positivity) (by positivity)).2
    norm_num
  rw [Real.log_pow, Real.log_pow] at hpowers
  rw [Real.logb]
  apply (lt_div_iff₀ hlog2).2
  have hscaled : (7 / 2 : ℝ) * Real.log 2 < Real.log 14 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    simpa [mul_comm] using hpowers
  exact hscaled

/-- **The actual-rate entropy value is strictly above the known exact pin.** -/
theorem prizeDeltaStar_one_eighth_fourteen_gt_three_fourths :
    (3 / 4 : ℝ) < prizeDeltaStar (1 / 8 : ℝ) 14 := by
  have hH : Real.binEntropy (1 / 8 : ℝ) < (2 / 5 : ℝ) :=
    binEntropy_one_eighth_lt_two_fifths
  have hlogb : (7 / 2 : ℝ) < Real.logb 2 14 :=
    seven_halves_lt_logb_two_fourteen
  have hlogbpos : 0 < Real.logb 2 14 := by linarith
  have hratio : Real.binEntropy (1 / 8 : ℝ) / Real.logb 2 14 < (1 / 8 : ℝ) := by
    rw [div_lt_iff₀ hlogbpos]
    have hHpos : 0 < Real.binEntropy (1 / 8 : ℝ) :=
      Real.binEntropy_pos (by norm_num) (by norm_num)
    nlinarith
  unfold prizeDeltaStar
  norm_num
  linarith

/-- The generic entropy equality remains false when supplied the actual dimension-one rate
`1/8` and the actual list budget `14`. -/
theorem actualRateEntropyPin_degreeZero_F12289_REFUTED :
    (mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
        (evalCode (4043 : ZMod 12289) 8 0) ((14 : ℝ≥0∞) / (12289 : ℝ≥0∞)) : ℝ)
      ≠ prizeDeltaStar (1 / 8 : ℝ) 14 := by
  rw [deltaStar_pin_F12289]
  norm_num
  exact ne_of_lt prizeDeltaStar_one_eighth_fourteen_gt_three_fourths

/-- **Machine-checked counterexample to `PrizePinConjecture` as stated.**

The degree-zero code has actual dimension one and rate `1/8`, but the conjecture passes the
degree ratio `0/8` to `prizeDeltaStar`.  Its two claimed values are therefore `3/4` and `1`.
-/
theorem prizePinConjecture_degreeZero_F12289_REFUTED :
    ¬ PrizePinConjecture (p := 12289) (n := 8) (4043 : ZMod 12289) 0
      ((14 : ℝ≥0∞) / (12289 : ℝ≥0∞)) := by
  intro hpin
  unfold PrizePinConjecture at hpin
  rw [deltaStar_pin_F12289] at hpin
  have hrate : (((0 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = 0 := by norm_num
  rw [hrate, prizeDeltaStar_zero_rate] at hpin
  norm_num at hpin

end ProximityGap.PrizeEntropy

/-! ## Axiom audit -/
#print axioms ProximityGap.PrizeEntropy.prizeDeltaStar_zero_rate
#print axioms ProximityGap.PrizeEntropy.binEntropy_one_eighth_exact
#print axioms ProximityGap.PrizeEntropy.binEntropy_one_eighth_lt_two_fifths
#print axioms ProximityGap.PrizeEntropy.seven_halves_lt_logb_two_fourteen
#print axioms ProximityGap.PrizeEntropy.prizeDeltaStar_one_eighth_fourteen_gt_three_fourths
#print axioms ProximityGap.PrizeEntropy.actualRateEntropyPin_degreeZero_F12289_REFUTED
#print axioms ProximityGap.PrizeEntropy.prizePinConjecture_degreeZero_F12289_REFUTED
