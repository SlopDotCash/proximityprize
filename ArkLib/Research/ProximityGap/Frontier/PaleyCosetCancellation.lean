/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.MobiusSeamCoordinateSupply
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.Linarith

/-!
# Paley discrepancy for unions of cosets at the second prize prime

Multiplication by a quadratic nonresidue changes the sign of the quadratic character.
The double sum on two sets preserved by this multiplication vanishes. On the second
production domain its order-`2^30` generator is a nonresidue, so the identity applies
to any two unions of its multiplicative cosets. A common fractional linear transformation
of two sets away from its pole multiplies each character entry by a determinant sign
and one sign from each denominator.
-/

namespace ProximityGap.PaleyCosetCancellation

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
private theorem sum_dilated (S : Finset F) {u : F} (hu : u ≠ 0)
    (hS : ∀ x ∈ S, u * x ∈ S) (f : F → ℤ) :
    ∑ x ∈ S, f (u * x) = ∑ x ∈ S, f x := by
  classical
  have himage : S.image (u * ·) = S := by
    apply Finset.eq_of_subset_of_card_le
    · simpa only [Finset.image_subset_iff] using hS
    · rw [Finset.card_image_of_injective _ (mul_right_injective₀ hu)]
  calc
    _ = ∑ x ∈ S.image (u * ·), f x := (Finset.sum_image (mul_right_injective₀ hu).injOn).symm
    _ = _ := by rw [himage]

/-- Simultaneous invariance under any nonsquare multiplier gives zero discrepancy. -/
theorem sum_eq_zero_of_dilation (A B : Finset F) {u : F} (hu : quadraticChar F u = -1)
    (hA : ∀ a ∈ A, u * a ∈ A) (hB : ∀ b ∈ B, u * b ∈ B) :
    ∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a - b) = 0 := by
  have h₀ : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hneg : (∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a - b)) =
      -(∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a - b)) := calc
    _ = ∑ a ∈ A, ∑ b ∈ B, quadraticChar F (u * a - b) :=
      (sum_dilated A h₀ hA (fun a => ∑ b ∈ B, quadraticChar F (a - b))).symm
    _ = ∑ a ∈ A, ∑ b ∈ B, quadraticChar F (u * a - u * b) := by
      apply Finset.sum_congr rfl
      intro a _
      exact (sum_dilated B h₀ hB (fun b => quadraticChar F (u * a - b))).symm
    _ = _ := by simp_rw [← mul_sub, map_mul, hu, neg_one_mul, Finset.sum_neg_distrib]
  omega

/-- Number of sites lost under one multiplicative shift. -/
def shiftLoss (S : Finset F) (u : F) : ℕ := (S \ S.image (u * ·)).card

private theorem abs_sum_le_card_mul {α : Type*} (S : Finset α) (f : α → ℤ) (c : ℤ)
    (hc : ∀ x, |f x| ≤ c) : |∑ x ∈ S, f x| ≤ S.card * c := by
  exact (Finset.abs_sum_le_sum_abs ..).trans (by simpa using
    (Finset.sum_le_sum (s := S) (g := fun _ => c) (fun x _ => hc x)))

omit [Fintype F] in
private theorem sum_shift_change (S : Finset F) {u : F} (hu : u ≠ 0) (f : F → ℤ) (c : ℤ)
    (hf : ∀ x, |f x| ≤ c) :
    |(∑ x ∈ S, f x) - ∑ x ∈ S, f (u*x)| ≤ 2 * shiftLoss S u * c := by
  classical
  let U := S.image (u * ·)
  have hcard : U.card = S.card := card_image_of_injective S (mul_right_injective₀ hu)
  have heq : (U \ S).card = (S \ U).card := card_sdiff_comm hcard
  have hdiff : (∑ x ∈ S, f x) - ∑ x ∈ S, f (u*x) =
      (∑ x ∈ S \ U, f x) - ∑ x ∈ U \ S, f x := by
    have hs : ∑ x ∈ U, f x = ∑ x ∈ S, f (u*x) :=
      Finset.sum_image (mul_right_injective₀ hu).injOn
    rw [← hs, ← sum_inter_add_sum_sdiff S U f, ← sum_inter_add_sum_sdiff U S f,
      Finset.inter_comm U S]
    ring
  rw [hdiff]
  apply (abs_sub _ _).trans
  have h₁ := abs_sum_le_card_mul (S \ U) f c hf
  have h₂ := abs_sum_le_card_mul (U \ S) f c hf
  rw [heq] at h₂
  change _ ≤ 2 * ((S \ U).card : ℤ) * c
  linarith

/-- The signed discrepancy is bounded by the number of sites lost at either boundary,
weighted by the size of the other set. -/
theorem discrepancy_le_shiftLoss (A B : Finset F) {u : F} (hu : quadraticChar F u = -1) :
    |∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a-b)| ≤
      (shiftLoss A u : ℤ) * B.card + (shiftLoss B u : ℤ) * A.card := by
  have h₀ : u ≠ 0 := by intro h; simp [h] at hu
  have hχ (v : F) : |quadraticChar F v| ≤ 1 := by
    by_cases hv : v = 0
    · simp [hv]
    · rcases quadraticChar_dichotomy hv with h | h <;> simp [h]
  let S := ∑ a ∈ A, ∑ b ∈ B, quadraticChar F (a-b)
  let V := ∑ a ∈ A, ∑ b ∈ B, quadraticChar F (u*a-b)
  have h₁ : |S - V| ≤ 2 * shiftLoss A u * B.card := by
    apply sum_shift_change A h₀ _ _
    intro a
    simpa using abs_sum_le_card_mul B (fun b => quadraticChar F (a-b)) 1 (fun b => hχ _)
  have hcol (b : F) : |∑ a ∈ A, quadraticChar F (u*a-b)| ≤ A.card := by
    simpa using abs_sum_le_card_mul A (fun a => quadraticChar F (u*a-b)) 1 (fun a => hχ _)
  have h₂ := sum_shift_change B h₀ (fun b => ∑ a ∈ A, quadraticChar F (u*a-b)) A.card hcol
  have hsign : (∑ b ∈ B, ∑ a ∈ A, quadraticChar F (u*a-u*b)) = -S := by
    rw [Finset.sum_comm]
    simp only [S, ← mul_sub, map_mul, hu, neg_one_mul, sum_neg_distrib]
  rw [hsign, Finset.sum_comm] at h₂
  change |V - -S| ≤ _ at h₂
  have htriangle := abs_add_le (S - V) (V - -S)
  rw [show S - V + (V - -S) = 2*S by ring, abs_mul] at htriangle
  change |S| ≤ _
  norm_num at htriangle h₂
  linarith

/-- A geometric interval is a consecutive block of powers in a multiplicative orbit. -/
def geometricInterval (u a : F) (k : ℕ) : Finset F := (range k).image (fun i => a * u^i)

omit [Fintype F] in
private theorem interval_shiftLoss_le_one (u a : F) (k : ℕ) :
    shiftLoss (geometricInterval u a k) u ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  suffices h : ∀ x ∈ geometricInterval u a k \ (geometricInterval u a k).image (u * ·), x = a by
    intro x hx y hy
    exact (h x hx).trans (h y hy).symm
  intro x hx
  obtain ⟨hxS, hxU⟩ := mem_sdiff.mp hx
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hxS
  cases i with
  | zero => simp
  | succ j =>
    exfalso
    apply hxU
    refine mem_image.mpr ⟨a*u^j, mem_image.mpr ⟨j, mem_range.mpr (by simpa using
      (Nat.lt_of_succ_lt (mem_range.mp hi))), rfl⟩, ?_⟩
    rw [pow_succ]
    ring

/-- The discrepancy of two arbitrary geometric intervals in nonsquare orbits is at
most the sum of their sizes. -/
theorem geometric_intervals_discrepancy {u : F} (hu : quadraticChar F u = -1) (a b : F) (k l : ℕ) :
    let A := geometricInterval u a k
    let B := geometricInterval u b l
    |∑ x ∈ A, ∑ y ∈ B, quadraticChar F (x-y)| ≤ (A.card : ℤ) + B.card := by
  dsimp only
  apply (discrepancy_le_shiftLoss _ _ hu).trans
  have h₁ : (shiftLoss (geometricInterval u a k) u : ℤ) ≤ 1 := by
    exact_mod_cast interval_shiftLoss_le_one u a k
  have h₂ : (shiftLoss (geometricInterval u b l) u : ℤ) ≤ 1 := by
    exact_mod_cast interval_shiftLoss_le_one u b l
  nlinarith [mul_le_mul_of_nonneg_right h₁ (Int.natCast_nonneg (geometricInterval u b l).card),
    mul_le_mul_of_nonneg_right h₂ (Int.natCast_nonneg (geometricInterval u a k).card)]

/-- An element of even order and odd index is a quadratic nonresidue in a prime field. -/
theorem quadraticChar_of_odd_index {p h m : ℕ} [Fact p.Prime] {u : ZMod p}
    (hp : p ≠ 2) (hu : u ≠ 0) (hh : 0 < h) (hm : Odd m)
    (horder : orderOf u = h * 2) (hfield : p = 2 * (h * m) + 1) :
    quadraticChar (ZMod p) u = -1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ringChar.eq (ZMod p) p]
  rw [quadraticChar_eq_pow_of_char_ne_two hchar hu, ZMod.card]
  have hhalf : p / 2 = h * m := by omega
  have hne : u ^ (p / 2) ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [horder, hhalf] at hd
    have h₂ := Nat.dvd_of_mul_dvd_mul_left hh hd
    obtain ⟨k, hk⟩ := hm
    omega
  simp [hne]

open MobiusSeamCoordinateSupply (Mobius)

/-- On finite nonpoles a common fractional linear transformation changes the Paley
character matrix by the determinant character and by one sign for each index. -/
theorem mobius_character_difference (M : Mobius F) {x y : F} (hx : M.den x ≠ 0)
    (hy : M.den y ≠ 0) :
    quadraticChar F (M.value x - M.value y) =
      quadraticChar F M.det * quadraticChar F (M.den x) * quadraticChar F (M.den y) *
        quadraticChar F (x - y) := by
  have hdiff : (M.value x - M.value y) * (M.den x * M.den y) = M.det * (x - y) := by
    dsimp only [MobiusSeamCoordinateSupply.Mobius.value]
    field_simp [hx, hy]
    dsimp [MobiusSeamCoordinateSupply.Mobius.num, MobiusSeamCoordinateSupply.Mobius.den,
      MobiusSeamCoordinateSupply.Mobius.det]
    ring
  have hs := quadraticChar_sq_one (mul_ne_zero hx hy)
  calc
    _ = quadraticChar F (M.value x - M.value y) * quadraticChar F (M.den x * M.den y) ^ 2 :=
      by rw [hs, mul_one]
    _ = _ := by rw [pow_two, ← mul_assoc, ← map_mul, hdiff, map_mul, map_mul]; ring

/-- The weighted character sum on two Möbius images equals the original bilinear form
with signed row and column weights. This applies with real or complex weights. -/
theorem mobius_weighted_image_sum {R : Type*} [CommRing R] (M : Mobius F)
    (hdet : M.det ≠ 0) (A B : Finset F)
    (hA : ∀ x ∈ A, M.den x ≠ 0) (hB : ∀ y ∈ B, M.den y ≠ 0) (r s : F → R) :
    (∑ x ∈ A.image M.value, ∑ y ∈ B.image M.value, r x * s y * (quadraticChar F (x - y) : R)) =
      (quadraticChar F M.det : R) *
        ∑ x ∈ A, ∑ y ∈ B, (r (M.value x) * (quadraticChar F (M.den x) : R)) *
          (s (M.value y) * (quadraticChar F (M.den y) : R)) * (quadraticChar F (x - y) : R) := by
  classical
  have injA := fun x hx y hy => M.injective_on_finite hdet (hA x hx) (hA y hy)
  have injB := fun x hx y hy => M.injective_on_finite hdet (hB x hx) (hB y hy)
  rw [Finset.sum_image injA, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_image injB, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [mobius_character_difference M (hA x hx) (hB y hy)]
  push_cast
  ring

/-- The denominator signs and reindexing in the Möbius pullback preserve squared real weights. -/
theorem mobius_pullback_sum_sq (M : Mobius F) (hdet : M.det ≠ 0) (A : Finset F)
    (hA : ∀ x ∈ A, M.den x ≠ 0) (r : F → ℝ) :
    ∑ x ∈ A, (r (M.value x) * (quadraticChar F (M.den x) : ℝ)) ^ 2 =
      ∑ y ∈ A.image M.value, (r y) ^ 2 := by
  classical
  rw [Finset.sum_image (fun x hx y hy => M.injective_on_finite hdet (hA x hx) (hA y hy))]
  apply Finset.sum_congr rfl
  intro x hx
  have hχ : (quadraticChar F (M.den x) : ℝ) ^ 2 = 1 := by
    exact_mod_cast quadraticChar_sq_one (hA x hx)
  rw [mul_pow, hχ, mul_one]

/-- A squared operator-norm bound on the original Paley matrix has exactly the same
constant on the two images. The row and column supports may be different. -/
theorem mobius_image_bilinear_bound (M : Mobius F) (hdet : M.det ≠ 0) (A B : Finset F)
    (hA : ∀ x ∈ A, M.den x ≠ 0) (hB : ∀ y ∈ B, M.den y ≠ 0) (K : ℝ)
    (hK : ∀ r s : F → ℝ,
      (∑ x ∈ A, ∑ y ∈ B, r x * s y * (quadraticChar F (x - y) : ℝ)) ^ 2 ≤
        K ^ 2 * (∑ x ∈ A, r x ^ 2) * (∑ y ∈ B, s y ^ 2))
    (r s : F → ℝ) :
    (∑ x ∈ A.image M.value, ∑ y ∈ B.image M.value,
      r x * s y * (quadraticChar F (x - y) : ℝ)) ^ 2 ≤
        K ^ 2 * (∑ x ∈ A.image M.value, r x ^ 2) * (∑ y ∈ B.image M.value, s y ^ 2) := by
  rw [mobius_weighted_image_sum M hdet A B hA hB r s, mul_pow]
  have hχ : (quadraticChar F M.det : ℝ) ^ 2 = 1 := by
    exact_mod_cast quadraticChar_sq_one hdet
  rw [hχ, one_mul, ← mobius_pullback_sum_sq M hdet A hA r,
    ← mobius_pullback_sum_sq M hdet B hB s]
  exact hK _ _

#print axioms mobius_image_bilinear_bound
#print axioms mobius_character_difference
#print axioms mobius_weighted_image_sum
#print axioms mobius_pullback_sum_sq

section SecondPrime

open ArkLib.ProximityGap.PrizeShapePrimeP30Second

local instance : Fact P.Prime := ⟨prime_P⟩

/-- The actual generator of the second production domain interchanges squares and nonsquares. -/
theorem second_generator_character : quadraticChar (ZMod P) g = -1 := by
  apply quadraticChar_of_odd_index (h := 2^29) (m := 2 * 2^128 + 13)
  · decide
  · decide
  · decide
  · exact ⟨2^128 + 6, by decide⟩
  · exact orderOf_g
  · decide

/-- Exact cancellation on every pair of sets invariant under the second production generator. -/
theorem second_prime_sum_eq_zero (A B : Finset (ZMod P))
    (hA : ∀ a ∈ A, g * a ∈ A) (hB : ∀ b ∈ B, g * b ∈ B) :
    ∑ a ∈ A, ∑ b ∈ B, quadraticChar (ZMod P) (a - b) = 0 :=
  sum_eq_zero_of_dilation A B second_generator_character hA hB

/-- For nonzero target values the fibers are cosets of the order-`2^30` subgroup.
The zero fiber can be included as well. -/
theorem second_prime_coset_unions (S T : Finset (ZMod P)) :
    ∑ a ∈ univ.filter (fun x : ZMod P => x ^ (2^30 : ℕ) ∈ S),
      ∑ b ∈ univ.filter (fun x : ZMod P => x ^ (2^30 : ℕ) ∈ T),
        quadraticChar (ZMod P) (a - b) = 0 := by
  have hg : g ^ (2^30 : ℕ) = 1 := by rw [← orderOf_g, pow_orderOf_eq_one]
  apply second_prime_sum_eq_zero <;> intro x hx <;>
    simpa only [mem_filter, mem_univ, true_and, mul_pow, hg, one_mul] using hx

/-- Arbitrary geometric subintervals of any two cosets at the second production prime. -/
theorem second_prime_interval_discrepancy (a b : ZMod P) (k l : ℕ) :
    let A := geometricInterval g a k
    let B := geometricInterval g b l
    |∑ x ∈ A, ∑ y ∈ B, quadraticChar (ZMod P) (x-y)| ≤ (A.card : ℤ) + B.card :=
  geometric_intervals_discrepancy second_generator_character a b k l

#print axioms second_prime_interval_discrepancy
#print axioms discrepancy_le_shiftLoss
#print axioms sum_eq_zero_of_dilation
#print axioms quadraticChar_of_odd_index
#print axioms second_prime_coset_unions

end SecondPrime
end ProximityGap.PaleyCosetCancellation
