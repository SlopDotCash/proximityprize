/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothCosetCubicSeed

/-! # Two completely split cubic pencils with a common member on sixteenth roots -/

set_option autoImplicit false
noncomputable section

namespace ArkLib.ProximityGap.Frontier.TwoCubicExtraSeed
variable {F : Type} [Field F]

/-- Monic cubic at three specified powers of the generator. -/
def cubic (w t : F) (a b c : ℕ) : F :=
  (t - w ^ a) * (t - w ^ b) * (t - w ^ c)

/-- Leading coefficient of the new outer cubic. -/
def scale (w : F) : F := 1 - w ^ 4 - w ^ 6

/-- The old head, followed by the two exterior cubics. -/
def values (w t : F) : Fin 4 → F :=
  ![0, cubic w t 0 1 8, w ^ 2 * cubic w t 2 9 10, scale w * cubic w t 6 9 14]

/-- Exact factorization of the cubic difference. -/
theorem w_minus_v (w t : F) (hw : w ^ 8 = -1) :
    cubic w t 0 1 8 - scale w * cubic w t 6 9 14 =
      (1 - scale w) * cubic w t 7 11 13 := by
  have z : w ^ 8 + 1 = 0 := by rw [hw]; ring
  unfold scale cubic
  linear_combination (w ^ 29 - w ^ 25 + w ^ 17 - w ^ 9 +
    (-w ^ 22 + w ^ 21 - w ^ 20 + w ^ 19 - w ^ 16 - w ^ 15 + w ^ 8 + w) * t +
    (-w ^ 12 + w ^ 11 - w ^ 10 + 2 * w ^ 9 + w ^ 6 - w - 1) * t ^ 2) * z

/-- Exact factorization of the cubic difference. -/
theorem q_minus_v (w t : F) (hw : w ^ 8 = -1) :
    w ^ 2 * cubic w t 2 9 10 - scale w * cubic w t 6 9 14 =
      (w ^ 2 - scale w) * cubic w t 7 9 15 := by
  have z : w ^ 8 + 1 = 0 := by rw [hw]; ring
  unfold scale cubic
  linear_combination (w ^ 29 - w ^ 23 +
    (-w ^ 22 + w ^ 21 - 2 * w ^ 20 + w ^ 19 - w ^ 18 + w ^ 16 - w ^ 15 + w ^ 14 + w ^ 13) * t +
    (w ^ 13 - w ^ 12 + w ^ 11 - w ^ 10 + w ^ 9 - w ^ 7 + w ^ 6 - w ^ 4) * t ^ 2) * z

/-- All coefficients multiplying the six pairwise factorizations are nonzero. -/
theorem units (w : F) (hw : orderOf w = 16) : w ≠ 0 ∧ w ^ 2 ≠ 1 ∧
    scale w ≠ 0 ∧ scale w ≠ 1 ∧ w ^ 2 ≠ scale w := by
  have neq {a b : ℕ} (ha : a < 16) (hb : b < 16) (hab : a ≠ b) : w ^ a ≠ w ^ b :=
    fun h => hab (pow_injOn_Iio_orderOf (x := w) (by change a < orderOf w; rwa [hw])
      (by change b < orderOf w; rwa [hw]) h)
  have h8 : w ^ 8 = -1 := by
    have h : (w ^ 8) ^ 2 = 1 := by rw [← pow_mul, show 8 * 2 = orderOf w by omega, pow_orderOf_eq_one]
    exact (sq_eq_one_iff.mp h).resolve_left (by simpa using neq (a := 8) (b := 0) (by decide) (by decide) (by decide))
  have ratio : (w ^ 5 - w ^ 7) * scale w = w - w ^ 7 := by
    unfold scale
    have z : w ^ 8 + 1 = 0 := by rw [h8]; ring
    linear_combination (w ^ 5 - w) * z
  have nonzero : scale w ≠ 0 := by
    intro h
    rw [h, mul_zero] at ratio
    exact neq (a := 1) (b := 7) (by decide) (by decide) (by decide) (by simpa using (sub_eq_zero.mp ratio.symm))
  refine ⟨fun z => by simp [z] at h8, by simpa using neq (a := 2) (b := 0) (by decide) (by decide) (by decide),
    nonzero, ?_, ?_⟩
  · intro h
    rw [h, mul_one] at ratio
    exact neq (a := 5) (b := 1) (by decide) (by decide) (by decide) (by simpa using sub_left_inj.mp ratio)
  · intro h
    have e := q_minus_v w (w ^ 2) h8
    rw [sub_eq_zero.mpr h, zero_mul] at e
    simp only [cubic, sub_self, zero_mul, mul_zero, zero_sub, neg_eq_zero] at e
    rcases mul_eq_zero.mp e with z | z
    · exact nonzero z
    · rcases mul_eq_zero.mp z with two | z
      · rcases mul_eq_zero.mp two with z | z
        · exact neq (by decide) (by decide) (by decide) (sub_eq_zero.mp z)
        · exact neq (by decide) (by decide) (by decide) (sub_eq_zero.mp z)
      · exact neq (by decide) (by decide) (by decide) (sub_eq_zero.mp z)

#print axioms w_minus_v
#print axioms q_minus_v
#print axioms units

end ArkLib.ProximityGap.Frontier.TwoCubicExtraSeed
