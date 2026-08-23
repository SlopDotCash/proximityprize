/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch

/-!
# The μ = 6 literal-budget band table (#371): feasibility certificates for `n = 64`

The literal-budget pin programme (`LiteralBudgetPin.lean`: the first in-window `δ*` at
`ε* = 2⁻¹²⁸`, at `μ = 5`) is blocked at `μ = 6` by exactly one inequality: the bad-side
threshold `(2^μ)^{2^{μ−1}} = 2¹⁹² < p` of `kkh26_epsMCA_lower_bound`, which enters through
the ℓ¹ resultant bound `natAbs_resultant_cyclotomic_le`.  The proposed Landau ℓ²-sharpening
(see the #371 thread) cuts it to `≈ 2^{127.5}`; the `_of_not_dvd` divisibility route
(`kkh26_lemma1_of_not_dvd`) removes it entirely at primes avoiding the collision resultants.

**This file lands the arithmetic that is unconditional either way**: for every rung
`r = 2..13` at `μ = 6` (`n = 64`, domain size 64, dimension `r − 1`),

* the literal `ε* = 2⁻¹²⁸` band is NONEMPTY: `C(64,r)/r < 2^r·C(32,r)`
  (`mu6_band_open_r*`), so the budget band is the field-size window
  `q ∈ [⌊C(64,r)/r⌋·2¹²⁸, 2^r·C(32,r)·2¹²⁸)` — sitting in `[2¹³⁸, 2¹⁷⁰)`, entirely
  *above* the sharpened threshold and *below* the current one;
* the pinned radius `1 − r/64` is beyond Johnson: `r² < (r−1)·64` (`mu6_beyond_johnson_r*`).

Once any route discharges the bad side at a prime inside a window, the corresponding pin
`mcaDeltaStar(evalCode g 64 (r−2), 1/2¹²⁸) = 1 − r/64` fires through
`kkh26_march_deltaStar_pin` + the `StaircaseBandTheorem` budget bridges, exactly as at
`μ = 5`.  (`r = 13` is not the wall — deeper rungs stay open past it; `13` is where this
table stops, already past the `r ≈ 1.6·√n` reach of every clean criterion.)

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

namespace ArkLib.ProximityGap.Mu6LiteralBands

/-- Rung `r = 2` (dimension 1): band `[1008·2¹²⁸, 1984·2¹²⁸)` is nonempty. -/
theorem mu6_band_open_r2 : (2 ^ 6).choose 2 / 2 < 2 ^ 2 * (2 ^ 5).choose 2 := by
  have h1 : (64 : ℕ).choose 2 = 2016 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (32 : ℕ).choose 2 = 496 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (64 : ℕ).choose 2 / 2 < 2 ^ 2 * (32 : ℕ).choose 2
  rw [h1, h2]
  norm_num

/-- Rung `r = 2`: the pinned radius `1 − 2/64` is beyond Johnson (`4 < 64`). -/
theorem mu6_beyond_johnson_r2 : 2 * 2 < (2 - 1) * 2 ^ 6 := by norm_num

/-- Rung `r = 3` (dimension 2): band `[13888·2¹²⁸, 39680·2¹²⁸)` is nonempty. -/
theorem mu6_band_open_r3 : (2 ^ 6).choose 3 / 3 < 2 ^ 3 * (2 ^ 5).choose 3 := by
  have h1 : (64 : ℕ).choose 3 = 41664 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (32 : ℕ).choose 3 = 4960 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (64 : ℕ).choose 3 / 3 < 2 ^ 3 * (32 : ℕ).choose 3
  rw [h1, h2]
  norm_num

/-- Rung `r = 3`: the pinned radius `1 − 3/64` is beyond Johnson (`9 < 128`). -/
theorem mu6_beyond_johnson_r3 : 3 * 3 < (3 - 1) * 2 ^ 6 := by norm_num

/-- Rung `r = 4` (dimension 3): band `[158844·2¹²⁸, 575360·2¹²⁸)` is nonempty. -/
theorem mu6_band_open_r4 : (2 ^ 6).choose 4 / 4 < 2 ^ 4 * (2 ^ 5).choose 4 := by
  have h1 : (64 : ℕ).choose 4 = 635376 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (32 : ℕ).choose 4 = 35960 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (64 : ℕ).choose 4 / 4 < 2 ^ 4 * (32 : ℕ).choose 4
  rw [h1, h2]
  norm_num

/-- Rung `r = 4`: the pinned radius `1 − 4/64` is beyond Johnson (`16 < 192`). -/
theorem mu6_beyond_johnson_r4 : 4 * 4 < (4 - 1) * 2 ^ 6 := by norm_num

/-- Rung `r = 5` (dimension 4): band `[1524902·2¹²⁸, 6444032·2¹²⁸)` is nonempty. -/
theorem mu6_band_open_r5 : (2 ^ 6).choose 5 / 5 < 2 ^ 5 * (2 ^ 5).choose 5 := by
  have h1 : (64 : ℕ).choose 5 = 7624512 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (32 : ℕ).choose 5 = 201376 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (64 : ℕ).choose 5 / 5 < 2 ^ 5 * (32 : ℕ).choose 5
  rw [h1, h2]
  norm_num

/-- Rung `r = 5`: the pinned radius `1 − 5/64` is beyond Johnson (`25 < 256`). -/
theorem mu6_beyond_johnson_r5 : 5 * 5 < (5 - 1) * 2 ^ 6 := by norm_num

/-- Rung `r = 6` (dimension 5): band `[12495728·2¹²⁸, 57996288·2¹²⁸)` is nonempty. -/
theorem mu6_band_open_r6 : (2 ^ 6).choose 6 / 6 < 2 ^ 6 * (2 ^ 5).choose 6 := by
  have h1 : (64 : ℕ).choose 6 = 74974368 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (32 : ℕ).choose 6 = 906192 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (64 : ℕ).choose 6 / 6 < 2 ^ 6 * (32 : ℕ).choose 6
  rw [h1, h2]
  norm_num

/-- Rung `r = 6`: the pinned radius `1 − 6/64` is beyond Johnson (`36 < 320`). -/
theorem mu6_beyond_johnson_r6 : 6 * 6 < (6 - 1) * 2 ^ 6 := by norm_num

/-- Rung `r = 7` (dimension 6): band `[88745170·2¹²⁸, 430829568·2¹²⁸)` is nonempty. -/
theorem mu6_band_open_r7 : (2 ^ 6).choose 7 / 7 < 2 ^ 7 * (2 ^ 5).choose 7 := by
  have h1 : (64 : ℕ).choose 7 = 621216192 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (32 : ℕ).choose 7 = 3365856 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (64 : ℕ).choose 7 / 7 < 2 ^ 7 * (32 : ℕ).choose 7
  rw [h1, h2]
  norm_num

/-- Rung `r = 7`: the pinned radius `1 − 7/64` is beyond Johnson (`49 < 384`). -/
theorem mu6_beyond_johnson_r7 : 7 * 7 < (7 - 1) * 2 ^ 6 := by norm_num

/-- Rung `r = 8` (dimension 7): band `[553270671·2¹²⁸, 2692684800·2¹²⁸)` is nonempty. -/
theorem mu6_band_open_r8 : (2 ^ 6).choose 8 / 8 < 2 ^ 8 * (2 ^ 5).choose 8 := by
  have h1 : (64 : ℕ).choose 8 = 4426165368 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (32 : ℕ).choose 8 = 10518300 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (64 : ℕ).choose 8 / 8 < 2 ^ 8 * (32 : ℕ).choose 8
  rw [h1, h2]
  norm_num

/-- Rung `r = 8`: the pinned radius `1 − 8/64` is beyond Johnson (`64 < 448`). -/
theorem mu6_beyond_johnson_r8 : 8 * 8 < (8 - 1) * 2 ^ 6 := by norm_num

/-- Rung `r = 9` (dimension 8): band `[3060064945·2¹²⁸, 14360985600·2¹²⁸)` is nonempty. -/
theorem mu6_band_open_r9 : (2 ^ 6).choose 9 / 9 < 2 ^ 9 * (2 ^ 5).choose 9 := by
  have h1 : (64 : ℕ).choose 9 = 27540584512 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (32 : ℕ).choose 9 = 28048800 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (64 : ℕ).choose 9 / 9 < 2 ^ 9 * (32 : ℕ).choose 9
  rw [h1, h2]
  norm_num

/-- Rung `r = 9`: the pinned radius `1 − 9/64` is beyond Johnson (`81 < 512`). -/
theorem mu6_beyond_johnson_r9 : 9 * 9 < (9 - 1) * 2 ^ 6 := by norm_num

/-- Rung `r = 10` (dimension 9): band `[15147321481·2¹²⁸, 66060533760·2¹²⁸)` is nonempty. -/
theorem mu6_band_open_r10 : (2 ^ 6).choose 10 / 10 < 2 ^ 10 * (2 ^ 5).choose 10 := by
  have h1 : (64 : ℕ).choose 10 = 151473214816 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (32 : ℕ).choose 10 = 64512240 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (64 : ℕ).choose 10 / 10 < 2 ^ 10 * (32 : ℕ).choose 10
  rw [h1, h2]
  norm_num

/-- Rung `r = 10`: the pinned radius `1 − 10/64` is beyond Johnson (`100 < 576`). -/
theorem mu6_beyond_johnson_r10 : 10 * 10 < (10 - 1) * 2 ^ 6 := by norm_num

/-- Rung `r = 11` (dimension 10): band `[67599616529·2¹²⁸, 264242135040·2¹²⁸)` is nonempty. -/
theorem mu6_band_open_r11 : (2 ^ 6).choose 11 / 11 < 2 ^ 11 * (2 ^ 5).choose 11 := by
  have h1 : (64 : ℕ).choose 11 = 743595781824 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (32 : ℕ).choose 11 = 129024480 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (64 : ℕ).choose 11 / 11 < 2 ^ 11 * (32 : ℕ).choose 11
  rw [h1, h2]
  norm_num

/-- Rung `r = 11`: the pinned radius `1 − 11/64` is beyond Johnson (`121 < 640`). -/
theorem mu6_beyond_johnson_r11 : 11 * 11 < (11 - 1) * 2 ^ 6 := by norm_num

/-- Rung `r = 12` (dimension 11): band `[273684558588·2¹²⁸, 924847472640·2¹²⁸)` is nonempty. -/
theorem mu6_band_open_r12 : (2 ^ 6).choose 12 / 12 < 2 ^ 12 * (2 ^ 5).choose 12 := by
  have h1 : (64 : ℕ).choose 12 = 3284214703056 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (32 : ℕ).choose 12 = 225792840 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (64 : ℕ).choose 12 / 12 < 2 ^ 12 * (32 : ℕ).choose 12
  rw [h1, h2]
  norm_num

/-- Rung `r = 12`: the pinned radius `1 − 12/64` is beyond Johnson (`144 < 704`). -/
theorem mu6_beyond_johnson_r12 : 12 * 12 < (12 - 1) * 2 ^ 6 := by norm_num

/-- Rung `r = 13` (dimension 12): band `[1010527600940·2¹²⁸, 2845684531200·2¹²⁸)` is nonempty. -/
theorem mu6_band_open_r13 : (2 ^ 6).choose 13 / 13 < 2 ^ 13 * (2 ^ 5).choose 13 := by
  have h1 : (64 : ℕ).choose 13 = 13136858812224 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (32 : ℕ).choose 13 = 347373600 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (64 : ℕ).choose 13 / 13 < 2 ^ 13 * (32 : ℕ).choose 13
  rw [h1, h2]
  norm_num

/-- Rung `r = 13`: the pinned radius `1 − 13/64` is beyond Johnson (`169 < 768`). -/
theorem mu6_beyond_johnson_r13 : 13 * 13 < (13 - 1) * 2 ^ 6 := by norm_num

end ArkLib.ProximityGap.Mu6LiteralBands

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.Mu6LiteralBands.mu6_band_open_r2
#print axioms ArkLib.ProximityGap.Mu6LiteralBands.mu6_band_open_r3
#print axioms ArkLib.ProximityGap.Mu6LiteralBands.mu6_band_open_r4
#print axioms ArkLib.ProximityGap.Mu6LiteralBands.mu6_band_open_r5
#print axioms ArkLib.ProximityGap.Mu6LiteralBands.mu6_band_open_r6
#print axioms ArkLib.ProximityGap.Mu6LiteralBands.mu6_band_open_r7
#print axioms ArkLib.ProximityGap.Mu6LiteralBands.mu6_band_open_r8
#print axioms ArkLib.ProximityGap.Mu6LiteralBands.mu6_band_open_r9
#print axioms ArkLib.ProximityGap.Mu6LiteralBands.mu6_band_open_r10
#print axioms ArkLib.ProximityGap.Mu6LiteralBands.mu6_band_open_r11
#print axioms ArkLib.ProximityGap.Mu6LiteralBands.mu6_band_open_r12
#print axioms ArkLib.ProximityGap.Mu6LiteralBands.mu6_band_open_r13
