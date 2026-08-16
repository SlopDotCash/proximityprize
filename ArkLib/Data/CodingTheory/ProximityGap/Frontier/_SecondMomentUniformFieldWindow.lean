/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Uniform field-window arithmetic for the quotient second-moment ceiling

The quotient interpolation construction gives the lower bound

`(M - M^2 / p) / p <= epsMCA`.

At the security target `1 / Q`, strict badness is therefore supplied by the integer
inequality

`p^2 < Q * (M * p - M^2)`.

This file proves a rounded choice that works uniformly throughout the field window
`Q <= p < Q^2`:

`M := p / Q + 3`.

For `Q = 2^128`, this uses at most `2^128 + 2` quotient subsets for every
`p < 2^256`.  The final theorems certify that the four exact-rate dyadic quotient
rungs used by the bad-side construction have that much binomial supply.  Nothing here
asserts a matching good side or an equality for `deltaStar`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow

/-- In the window `Q <= p < Q^2`, the quotient `a = p / Q` lies in `[1,Q)`. -/
theorem quotient_window {Q p : Nat} (hQ : 1 <= Q) (hlo : Q <= p) (hhi : p < Q ^ 2) :
    1 <= p / Q ∧ p / Q < Q := by
  have hQpos : 0 < Q := by omega
  constructor
  · exact Nat.le_div_iff_mul_le hQpos |>.2 (by simpa using hlo)
  · apply (Nat.div_lt_iff_lt_mul hQpos).2
    simpa [pow_two, Nat.mul_comm] using hhi

/-- The rounded family size `M = p / Q + 3` remains below the field size. -/
theorem rounded_family_le_field {Q p : Nat} (hQ : 14 <= Q) (hlo : Q <= p) :
    p / Q + 3 <= p := by
  have hQpos : 0 < Q := by omega
  have ha : 1 <= p / Q :=
    Nat.le_div_iff_mul_le hQpos |>.2 (by simpa using hlo)
  have hmul : (p / Q) * Q <= p := Nat.div_mul_le_self p Q
  nlinarith

/-- The square of the rounded family size fits inside `M*p`, so the natural subtraction
in the second-moment numerator is exact rather than truncated past zero. -/
theorem rounded_family_sq_le_mul_field {Q p : Nat} (hQ : 14 <= Q) (hlo : Q <= p) :
    (p / Q + 3) ^ 2 <= (p / Q + 3) * p := by
  have hM := rounded_family_le_field hQ hlo
  simpa [pow_two] using Nat.mul_le_mul_left (p / Q + 3) hM

/-- The only nonlinear estimate needed by the field-window argument:
`(p/Q+3)^2 <= 2p`. -/
theorem rounded_family_sq_le_two_mul_field {Q p : Nat}
    (hQ : 14 <= Q) (hlo : Q <= p) (hhi : p < Q ^ 2) :
    (p / Q + 3) ^ 2 <= 2 * p := by
  let a := p / Q
  have ha : 1 <= a := (quotient_window (by omega) hlo hhi).1
  have haQ : a < Q := (quotient_window (by omega) hlo hhi).2
  have haQle : a * Q <= p := by
    simpa [a] using Nat.div_mul_le_self p Q
  have haa : a * a <= a * (Q - 1) := by
    apply Nat.mul_le_mul_left
    omega
  have htail : 5 * a + 9 <= 14 * a := by omega
  have hsquare : (a + 3) ^ 2 <= 2 * (a * Q) := by
    nlinarith
  calc
    (p / Q + 3) ^ 2 = (a + 3) ^ 2 := by rfl
    _ <= 2 * (a * Q) := hsquare
    _ <= 2 * p := Nat.mul_le_mul_left 2 haQle

/-- **Uniform strict second-moment numerator.**  If `14 <= Q <= p < Q^2` and
`M := p/Q+3`, then

`p^2 < Q * (M*p - M^2)`.

After division by `Q*p^2`, this is exactly
`1/Q < (M - M^2/p)/p`. -/
theorem field_sq_lt_security_mul_secondMoment_numerator {Q p : Nat}
    (hQ : 14 <= Q) (hlo : Q <= p) (hhi : p < Q ^ 2) :
    p ^ 2 < Q * ((p / Q + 3) * p - (p / Q + 3) ^ 2) := by
  let a := p / Q
  let M := a + 3
  have hp : 0 < p := by omega
  have hQpos : 0 < Q := by omega
  have hdivmod : a * Q + p % Q = p := by
    calc
      a * Q + p % Q = Q * a + p % Q := by ring
      _ = p := by simpa [a] using Nat.div_add_mod p Q
  have hmod : p % Q < Q := Nat.mod_lt p hQpos
  have hp_upper : p < Q * (a + 1) := by
    nlinarith
  have hM2 : M ^ 2 <= 2 * p := by
    simpa [M, a] using rounded_family_sq_le_two_mul_field hQ hlo hhi
  have hinside : (a + 1) * p <= M * p - M ^ 2 := by
    apply Nat.le_sub_of_add_le
    calc
      (a + 1) * p + M ^ 2 <= (a + 1) * p + 2 * p :=
        Nat.add_le_add_left hM2 _
      _ = M * p := by simp [M]; ring
  have hp_mul : p ^ 2 < (Q * (a + 1)) * p := by
    simpa [pow_two] using (Nat.mul_lt_mul_right hp).2 hp_upper
  calc
    p ^ 2 < (Q * (a + 1)) * p := hp_mul
    _ = Q * ((a + 1) * p) := by ring
    _ <= Q * (M * p - M ^ 2) := Nat.mul_le_mul_left Q hinside
    _ = Q * ((p / Q + 3) * p - (p / Q + 3) ^ 2) := by rfl

/-- Bundled form of the two integer facts consumed by the second-moment field-window bridge. -/
theorem rounded_family_uniform_field_window {Q p : Nat}
    (hQ : 14 <= Q) (hlo : Q <= p) (hhi : p < Q ^ 2) :
    (p / Q + 3) ^ 2 <= (p / Q + 3) * p ∧
      p ^ 2 < Q * ((p / Q + 3) * p - (p / Q + 3) ^ 2) :=
  ⟨rounded_family_sq_le_mul_field hQ hlo,
    field_sq_lt_security_mul_secondMoment_numerator hQ hlo hhi⟩

/-- The rounded family uses at most `Q+2` subsets throughout `p < Q^2`. -/
theorem rounded_family_le_security_add_two {Q p : Nat} (hQ : 1 <= Q)
    (hhi : p < Q ^ 2) :
    p / Q + 3 <= Q + 2 := by
  have hQpos : 0 < Q := by omega
  have ha : p / Q < Q := by
    apply (Nat.div_lt_iff_lt_mul hQpos).2
    simpa [pow_two, Nat.mul_comm] using hhi
  omega

/-! ## The `2^-128`, `p < 2^256` specialization -/

/-- At the prize security parameter, the rounded family has at most `2^128+2` members. -/
theorem prize_rounded_family_le {p : Nat} (hhi : p < 2 ^ 256) :
    p / 2 ^ 128 + 3 <= 2 ^ 128 + 2 := by
  apply rounded_family_le_security_add_two (Q := 2 ^ 128) (by norm_num)
  simpa [← pow_mul] using hhi

/-- At the prize security parameter, the rounded family gives a strict second-moment
bad-side numerator throughout `2^128 <= p < 2^256`. -/
theorem prize_field_sq_lt_secondMoment_numerator {p : Nat}
    (hlo : 2 ^ 128 <= p) (hhi : p < 2 ^ 256) :
    p ^ 2 < 2 ^ 128 *
      ((p / 2 ^ 128 + 3) * p - (p / 2 ^ 128 + 3) ^ 2) := by
  apply field_sq_lt_security_mul_secondMoment_numerator
  · norm_num
  · exact hlo
  · simpa [← pow_mul] using hhi

/-! ## Exact-rate dyadic quotient supplies

For rate `rho`, the construction uses `r = rho*s + 1`.  These are the first
deployed rungs used in the uniform `p < 2^256` table. -/

/-- No quotient size at most `128` can have the uniform `2^128+2` supply, regardless
of the chosen subset size.  Together with the explicit supply theorems below, this
certifies the first three entries as the first admissible dyadic quotient rungs. -/
theorem choose_supply_short_of_le_128 {s r : Nat} (hs : s <= 128) :
    Nat.choose s r < 2 ^ 128 + 2 := by
  calc
    Nat.choose s r <= 2 ^ s := Nat.choose_le_two_pow s r
    _ <= 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) hs
    _ < 2 ^ 128 + 2 := by omega

theorem rateHalf_s256_supply :
    2 ^ 128 + 2 <= Nat.choose 256 129 := by
  have hnum : ((2 ^ 128 + 2 : Nat) : Rat) <=
      ((256 + 1 - 129 : Nat) ^ 129 : Rat) / Nat.factorial 129 := by
    norm_num [Nat.factorial]
  have hchoose : (((256 + 1 - 129 : Nat) ^ 129 : Nat) : Rat) / Nat.factorial 129 <=
      (Nat.choose 256 129 : Rat) := Nat.pow_le_choose 129 256
  exact_mod_cast hnum.trans hchoose

theorem rateQuarter_s256_supply :
    2 ^ 128 + 2 <= Nat.choose 256 65 := by
  have hnum : ((2 ^ 128 + 2 : Nat) : Rat) <=
      ((256 + 1 - 65 : Nat) ^ 65 : Rat) / Nat.factorial 65 := by
    norm_num [Nat.factorial]
  have hchoose : (((256 + 1 - 65 : Nat) ^ 65 : Nat) : Rat) / Nat.factorial 65 <=
      (Nat.choose 256 65 : Rat) := Nat.pow_le_choose 65 256
  exact_mod_cast hnum.trans hchoose

theorem rateEighth_s256_supply :
    2 ^ 128 + 2 <= Nat.choose 256 33 := by
  have hnum : ((2 ^ 128 + 2 : Nat) : Rat) <=
      ((256 + 1 - 33 : Nat) ^ 33 : Rat) / Nat.factorial 33 := by
    norm_num [Nat.factorial]
  have hchoose : (((256 + 1 - 33 : Nat) ^ 33 : Nat) : Rat) / Nat.factorial 33 <=
      (Nat.choose 256 33 : Rat) := Nat.pow_le_choose 33 256
  exact_mod_cast hnum.trans hchoose

theorem rateSixteenth_s512_supply :
    2 ^ 128 + 2 <= Nat.choose 512 33 := by
  have hnum : ((2 ^ 128 + 2 : Nat) : Rat) <=
      ((512 + 1 - 33 : Nat) ^ 33 : Rat) / Nat.factorial 33 := by
    norm_num [Nat.factorial]
  have hchoose : (((512 + 1 - 33 : Nat) ^ 33 : Nat) : Rat) / Nat.factorial 33 <=
      (Nat.choose 512 33 : Rat) := Nat.pow_le_choose 33 512
  exact_mod_cast hnum.trans hchoose

/-- The immediately preceding half-rate dyadic rung does not have uniform supply. -/
theorem rateHalf_s128_supply_short :
    Nat.choose 128 65 < 2 ^ 128 + 2 := by
  exact (Nat.choose_lt_two_pow 128 65 (by norm_num)).trans (by omega)

/-- The immediately preceding quarter-rate dyadic rung does not have uniform supply. -/
theorem rateQuarter_s128_supply_short :
    Nat.choose 128 33 < 2 ^ 128 + 2 := by
  exact (Nat.choose_lt_two_pow 128 33 (by norm_num)).trans (by omega)

/-- The immediately preceding eighth-rate dyadic rung does not have uniform supply. -/
theorem rateEighth_s128_supply_short :
    Nat.choose 128 17 < 2 ^ 128 + 2 := by
  exact (Nat.choose_lt_two_pow 128 17 (by norm_num)).trans (by omega)

/-- The immediately preceding sixteenth-rate dyadic rung does not have uniform supply. -/
theorem rateSixteenth_s256_supply_short :
    Nat.choose 256 17 < 2 ^ 128 + 2 := by
  have hchoose : (Nat.choose 256 17 : Rat) <=
      (256 ^ 17 : Rat) / Nat.factorial 17 :=
    Nat.choose_le_pow_div 17 256
  have hnum : (256 ^ 17 : Rat) / Nat.factorial 17 < ((2 ^ 128 + 2 : Nat) : Rat) := by
    norm_num [Nat.factorial]
  exact_mod_cast hchoose.trans_lt hnum

end ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow

#print axioms ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow.quotient_window
#print axioms ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow.rounded_family_sq_le_mul_field
#print axioms ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow.field_sq_lt_security_mul_secondMoment_numerator
#print axioms ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow.rounded_family_uniform_field_window
#print axioms ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow.prize_field_sq_lt_secondMoment_numerator
#print axioms ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow.rateHalf_s256_supply
#print axioms ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow.rateQuarter_s256_supply
#print axioms ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow.rateEighth_s256_supply
#print axioms ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow.rateSixteenth_s512_supply
