/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DimTwoPin

/-!
# Arithmetic for the next KKH26 dimension-ladder rung (#371)

`KKH26DimTwoPin.lean` proves the `r = 3` slice by a triple-ownership count:
each bad scalar owns at least `2 * 3! = 12` ordered triples, and the resulting
bound beats the KKH26 ceiling spectrum.

This file records the cleared arithmetic target for the next rung (`r = 4`,
dimension three).  If the geometric ownership proof supplies the expected
`2 * 4! = 48` owned ordered quadruples per bad scalar, then the resulting
good-side count is strictly below the KKH26 ceiling spectrum for every
`μ ≥ 4`.

Honest scope: this is only the numeric separation.  The r-point bordered
Vandermonde/minimal-tuple geometry remains the real next proof obligation.
-/

namespace ArkLib.ProximityGap.KKH26LadderArithmetic

/-- For `h ≥ 8`, the cleared `r = 4` ladder inequality after cancelling the
formal common `h(h-1)` factor. -/
private lemma dimThree_core_poly_pos {h : ℕ} (hh : 8 ≤ h) :
    (2 * h - 1) * (2 * h - 3) < 8 * (h - 2) * (h - 3) := by
  obtain ⟨a, rfl⟩ : ∃ a, h = a + 8 := ⟨h - 8, by omega⟩
  have e1 : 2 * (a + 8) - 1 = 2 * a + 15 := by omega
  have e2 : 2 * (a + 8) - 3 = 2 * a + 13 := by omega
  have e3 : a + 8 - 2 = a + 6 := by omega
  have e4 : a + 8 - 3 = a + 5 := by omega
  calc
    (2 * (a + 8) - 1) * (2 * (a + 8) - 3)
        = (2 * a + 15) * (2 * a + 13) := by rw [e1, e2]
    _ = 4 * a * a + 56 * a + 195 := by ring
    _ < 4 * a * a + 56 * a + 195 + (4 * a * a + 32 * a + 45) :=
        Nat.lt_add_of_pos_right (by positivity)
    _ = 8 * a * a + 88 * a + 240 := by ring
    _ = 8 * (a + 6) * (a + 5) := by ring
    _ = 8 * (a + 8 - 2) * (a + 8 - 3) := by rw [e3, e4]

/-- The closed form for `24 * choose h 4`, written as a falling product. -/
private lemma twenty_four_mul_choose_four (h : ℕ) :
    24 * h.choose 4 = h * (h - 1) * (h - 2) * (h - 3) := by
  by_cases hh : 4 ≤ h
  · have hdvd : 24 ∣ h.descFactorial 4 := by
      have h := Nat.factorial_dvd_descFactorial h 4
      rwa [show Nat.factorial 4 = 24 from rfl] at h
    have hdesc : h.descFactorial 4 = h * (h - 1) * (h - 2) * (h - 3) := by
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero]
      ring
    rw [Nat.choose_eq_descFactorial_div_factorial, show Nat.factorial 4 = 24 from rfl,
      Nat.mul_div_cancel' hdvd, hdesc]
  · have hlt : h < 4 := Nat.lt_of_not_ge hh
    rw [Nat.choose_eq_zero_of_lt hlt]
    interval_cases h <;> norm_num

/-- **Cleared r = 4 ladder band separation.**  For `μ ≥ 4`, the proposed
dimension-three ownership bound with denominator `2 * 4! = 48` beats the KKH26
ceiling count after clearing the denominator:

`(2^μ)^{(4)} < 48 * 2^4 * C(2^{μ-1}, 4)`.

This is the arithmetic half of the next-rung target. -/
theorem dimThree_band_nonempty_cleared {μ : ℕ} (hμ : 4 ≤ μ) :
    2 ^ μ * (2 ^ μ - 1) * (2 ^ μ - 2) * (2 ^ μ - 3)
      < 48 * (2 ^ 4 * (2 ^ (μ - 1)).choose 4) := by
  obtain ⟨ν, rfl⟩ : ∃ ν, μ = ν + 4 := ⟨μ - 4, (Nat.sub_add_cancel hμ).symm⟩
  have hpow : (2 : ℕ) ^ (ν + 4) = 2 * (2 ^ (ν + 3)) := by
    rw [show ν + 4 = (ν + 3) + 1 by omega, pow_succ]
    ring
  have hchoose := twenty_four_mul_choose_four (2 ^ (ν + 3))
  have hcore : (2 * 2 ^ (ν + 3) - 1) * (2 * 2 ^ (ν + 3) - 3)
      < 8 * (2 ^ (ν + 3) - 2) * (2 ^ (ν + 3) - 3) :=
    dimThree_core_poly_pos (by
      calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (ν + 3) := Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [hpow, show ν + 4 - 1 = ν + 3 by omega]
  have hrhs : (48 : ℕ) * (2 ^ 4 * (2 ^ (ν + 3)).choose 4)
      = 32 * (24 * (2 ^ (ν + 3)).choose 4) := by ring
  rw [hrhs]
  rw [hchoose]
  set H : ℕ := 2 ^ (ν + 3) with hHdef
  have hH8 : 8 ≤ H := by
    rw [hHdef]
    calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (ν + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htwosub : 2 * H - 2 = 2 * (H - 1) := by omega
  have hfactor_pos : 0 < 2 * H * (2 * H - 2) := by
    have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH8
    have h2Hpos : 0 < 2 * H := Nat.mul_pos (by norm_num) hHpos
    have hsubpos : 0 < 2 * H - 2 := by omega
    exact Nat.mul_pos h2Hpos hsubpos
  calc
    2 * H * (2 * H - 1) * (2 * H - 2) * (2 * H - 3)
        = (2 * H * (2 * H - 2)) * ((2 * H - 1) * (2 * H - 3)) := by ring
    _ < (2 * H * (2 * H - 2)) * (8 * (H - 2) * (H - 3)) := by
        exact Nat.mul_lt_mul_of_pos_left (by simpa [hHdef] using hcore) hfactor_pos
    _ = 32 * (H * (H - 1) * (H - 2) * (H - 3)) := by
        rw [htwosub]
        ring

/-- **r = 4 ladder band nonemptiness.**  If the next geometric rung proves the
expected `2 * 4!` ownership count, then the induced left endpoint is strictly
below the KKH26 ceiling spectrum for every `μ ≥ 4`. -/
theorem dimThree_band_nonempty {μ : ℕ} (hμ : 4 ≤ μ) :
    2 ^ μ * (2 ^ μ - 1) * (2 ^ μ - 2) * (2 ^ μ - 3) / 48
      < 2 ^ 4 * (2 ^ (μ - 1)).choose 4 := by
  exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 48)).mpr
    (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      dimThree_band_nonempty_cleared hμ)

end ArkLib.ProximityGap.KKH26LadderArithmetic

/-! ## Axiom audit — arithmetic only. -/
#print axioms ArkLib.ProximityGap.KKH26LadderArithmetic.dimThree_band_nonempty_cleared
#print axioms ArkLib.ProximityGap.KKH26LadderArithmetic.dimThree_band_nonempty
