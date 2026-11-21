/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic

/-!
# Paley discrepancy for unions of cosets at the second prize prime

Multiplication by a quadratic nonresidue changes the sign of the quadratic character.
The double sum on two sets preserved by this multiplication vanishes. On the second
production domain its order-`2^30` generator is a nonresidue, so the identity applies
to any two unions of its multiplicative cosets.
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
