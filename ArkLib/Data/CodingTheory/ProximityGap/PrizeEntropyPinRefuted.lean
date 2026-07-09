/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PrizeEntropyDeltaStar
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DimOnePin

/-!
# The degree-parameterized entropy pin is refuted

`PrizePinConjecture g k epsilonStar` feeds `k / n` to the entropy formula while using
`evalCode g n k`.  In this code API, `k` is the polynomial degree bound, so the code has
dimension `k + 1`.  The mismatch is already decisive at degree zero.

For the eight-point constant code over `F_12289`, the unconditional KKH26 dimension-one
theorem proves that the operational threshold at budget `14/12289` is `3/4`.  The old
entropy expression sees the supplied rate as `0/8`; binary entropy vanishes at zero, so it
returns `1`, independently of the budget.  Hence this concrete instance of
`PrizePinConjecture` is false.

This refutes the Lean definition as stated.  It does not refute a corrected conjecture using
the actual rate `(k + 1) / n`, nor does it determine the four production prize instances.
-/

set_option autoImplicit false

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ProximityGap.PrizeEntropy
open ArkLib.ProximityGap.KKH26DimOne

namespace ProximityGap.PrizeEntropy

local instance fact_prime_12289_refutation : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- At the zero rate supplied by the stale degree parameter, the entropy candidate is `1`. -/
theorem prizeDeltaStar_zero_rate (B : ℝ) : prizeDeltaStar 0 B = 1 := by
  simp [prizeDeltaStar]

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
#print axioms ProximityGap.PrizeEntropy.prizePinConjecture_degreeZero_F12289_REFUTED
