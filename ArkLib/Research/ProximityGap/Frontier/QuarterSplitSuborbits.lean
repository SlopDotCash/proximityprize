/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-! # Suborbit sizes and branch orders forced by the parameterized subgroup estimate -/

namespace ProximityGap.QuarterSplitSuborbits

/-- The first coordinate of the powering stabilizer has at most two kernel
elements. Its image belongs to the group of roots of unity of the exponent. -/
theorem stabilizer_bound {G H : Type*} [Group G] [Group H] [Finite H]
    (first : G →* H) (hk : Nat.card first.ker ≤ 2) :
    Nat.card G ≤ 2 * Nat.card H := by
  rw [← Subgroup.card_ker_mul_card_range first]
  exact Nat.mul_le_mul hk (Nat.card_le_card_of_injective _ first.range.subtype_injective)

/-- The parameterized gcd estimate for an equal-bidegree component forces a
large suborbit, even if the full pair curve is reducible. -/
theorem subdegree {a : ℕ} (ha : 0 < a) (chi : ℝ)
    (gcd_bound : 78 * 268435454 * (a : ℝ) ≤ 14 * 1073741824 * a + 325 * chi)
    (adjunction : chi ≤ 2 * a ^ 2) : 9085508 ≤ a := by
  have h : (5905579876 : ℝ) * a ≤ 650 * a ^ 2 := by
    linarith only [gcd_bound, adjunction]
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hn : (5905579876 : ℝ) ≤ 650 * a := by
    apply (mul_le_mul_iff_of_pos_right ha').mp
    nlinarith only [h]
  have hint : 5905579876 ≤ 650 * a := by exact_mod_cast hn
  omega

/-- There are at most 29 non-singleton orbits of a sheet stabilizer and at
most two singleton orbits, the diagonal and the possible source involution. -/
theorem orbit_count {nontrivial singleton : ℕ} (hs : singleton ≤ 2)
    (degrees : 9085508 * nontrivial + singleton ≤ 268435454) :
    nontrivial ≤ 29 ∧ nontrivial + singleton ≤ 31 := by omega

/-- Use the sum of the component gcd bounds and the pair genus of a primitive
stage to obtain a linear constraint on its orbifold excess. -/
theorem primitive_excess {h m E euler : ℝ} (hh : 0 < h) (hm : 1 < m) (hE : 0 ≤ E + 2)
    (gcd_bound : 78 * 268435454 * h * (m - 1) ≤ 14 * 1073741824 * h * (m - 1) +
      325 * h ^ 2 * (euler + 4 * (m - 1)))
    (genus : euler * (E + 2) ≤ 2 * (m - 1) ^ 2 * E) :
    2 * (5905579876 - 1300 * h) ≤ (650 * (h * m + h) - 5905579876) * E := by
  have simple : 5905579876 * (m - 1) ≤ 325 * h * (euler + 4 * (m - 1)) := by
    apply (mul_le_mul_iff_of_pos_left hh).mp
    nlinarith only [gcd_bound]
  have bound := mul_le_mul_of_nonneg_right simple hE
  have g := mul_le_mul_of_nonneg_left genus (show 0 ≤ 325 * h by positivity)
  apply (mul_le_mul_iff_of_pos_right (sub_pos.mpr hm)).mp
  nlinarith only [bound, g]

/-- Named prefix degrees use the largest admissible source degree and also
give the branch excess of the full cover after the outer degree is charged. -/
theorem named {t h E : ℝ} (hpos : 0 ≤ E) (h2 : h ≤ 2)
    (odd : t = 19173961 ∨ t = 134217727 → h ≤ 1)
    (bound : 2 * (5905579876 - 1300 * h) ≤ (650 * (t + h) - 5905579876) * E) :
    (t = 19173961 → 1801168 / 1000000 < E) ∧
    (t = 38347922 → 620967 / 1000000 < E) ∧
    (t = 134217727 → 145214 / 1000000 < E) ∧
    (t = 268435454 → 70063 / 1000000 < E) := by
  have test (x a b : ℝ) (ht : t = x) (ha : h ≤ a)
      (cmp : (650 * (x + a) - 5905579876) * b < 2 * (5905579876 - 1300 * a))
      (pos : 0 < 650 * (x + a) - 5905579876) : b < E := by
    apply (mul_lt_mul_iff_of_pos_left pos).mp
    have prod := mul_le_mul_of_nonneg_right ha hpos
    rw [ht] at bound
    nlinarith only [bound, cmp, prod, ha]
  refine ⟨fun ht => test _ 1 _ ht (odd (Or.inl ht)) (by norm_num) (by norm_num),
    fun ht => test _ 2 _ ht h2 (by norm_num) (by norm_num),
    fun ht => test _ 1 _ ht (odd (Or.inr ht)) (by norm_num) (by norm_num),
    fun ht => test _ 2 _ ht h2 (by norm_num) (by norm_num)⟩

/-- Charge the four possible outer degrees to the excess lower bound for the
primitive stage. The full closure satisfies this same uniform restriction. -/
theorem full_excess {s E full : ℝ} (transfer : E ≤ s * full)
    (cases : (s = 14 ∧ 1801168 / 1000000 < E) ∨ (s = 7 ∧ 620967 / 1000000 < E) ∨
      (s = 2 ∧ 145214 / 1000000 < E) ∨ (s = 1 ∧ 70063 / 1000000 < E)) :
    70063 / 1000000 < full := by
  rcases cases with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> linarith

#print axioms stabilizer_bound
#print axioms full_excess
#print axioms subdegree
#print axioms orbit_count
#print axioms primitive_excess
#print axioms named
end ProximityGap.QuarterSplitSuborbits
