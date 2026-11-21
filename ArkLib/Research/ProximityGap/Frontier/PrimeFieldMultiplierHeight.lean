/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Low-height rational multipliers of prime-field subgroups

Equal power residues of two positive integers give a necessary and sufficient test for their
ratio to be an n-th root of unity. Counting prime divisors of the integer differences
bounds the number of primes having any such multiplier in a prescribed range.
-/

namespace ArkLib.ProximityGap.PrimeFieldMultiplierHeight

open Finset

/-- Collision of two positive integer powers on the finite interval from one through B. -/
def Collision (p n B : ℕ) : Prop :=
  ∃ a < B, ∃ b < a, (a + 1) ^ n ≡ (b + 1) ^ n [MOD p]

/-- A collision is precisely a rational multiplier whose n-th power is one, provided
the denominator is invertible in the field. -/
theorem ratio_pow_eq_one_iff {p n a b : ℕ} [Fact p.Prime] (hb : (b : ZMod p) ≠ 0) :
    (a / b : ZMod p) ^ n = 1 ↔ a ^ n ≡ b ^ n [MOD p] := by
  rw [div_pow, div_eq_iff (pow_ne_zero n hb), one_mul, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rfl


private def differences (n B : ℕ) :=
  ∏ a ∈ range B, ∏ b ∈ range a, ((a + 1) ^ n - (b + 1) ^ n)

private lemma divides_differences {p n B : ℕ} (hc : Collision p n B) :
    p ∣ differences n B := by
  obtain ⟨a, ha, b, hb, hm⟩ := hc
  apply hm.symm.dvd'.trans
  apply (Finset.dvd_prod_of_mem (fun c ↦ (a + 1) ^ n - (c + 1) ^ n) (Finset.mem_range.mpr hb)).trans
  unfold differences
  exact Finset.dvd_prod_of_mem (fun i ↦ ∏ c ∈ range i, ((i + 1) ^ n - (c + 1) ^ n))
    (Finset.mem_range.mpr ha)

private lemma positive_differences {n : ℕ} (hn : 0 < n) (B : ℕ) :
    0 < differences n B := by
  apply Finset.prod_pos
  intro a ha
  apply Finset.prod_pos
  intro b hb
  apply Nat.sub_pos_of_lt
  exact Nat.pow_lt_pow_left (by have := Finset.mem_range.mp hb; omega) hn.ne'

private lemma differences_le (n B : ℕ) :
    differences n B ≤ B ^ (n * B.choose 2) := calc
  _ ≤ ∏ a ∈ range B, ∏ _b ∈ range a, B ^ n := by
    apply Finset.prod_le_prod
    intro a ha
    apply Finset.prod_le_prod
    intro b _
    exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_left (by have := mem_range.mp ha; omega) _)
  _ = B ^ (n * B.choose 2) := by
    simp only [Finset.prod_const, Finset.card_range]
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id, Nat.choose_two_right, pow_mul]

/-- Counting all qualifying prime divisors gives a bound on every finite set of primes,
including primes in very short windows or in selected residue classes. -/
theorem exceptional_prime_power_bound {n B P : ℕ} (hn : 0 < n) (S : Finset ℕ)
    (h : ∀ p ∈ S, p.Prime ∧ P ≤ p ∧ Collision p n B) :
    P ^ S.card ≤ B ^ (n * B.choose 2) := calc
  _ = ∏ _p ∈ S, P := by simp
  _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod fun p hp ↦ (h p hp).2.1
  _ ≤ differences n B := Nat.le_of_dvd (positive_differences hn B) <|
    Finset.prod_primes_dvd _ (fun p hp ↦ (h p hp).1.prime)
      (fun p hp ↦ divides_differences (h p hp).2.2)
  _ ≤ _ := differences_le _ _

private lemma dyadic_mass {n l k : ℕ} (hn : 0 < n) (S : Finset ℕ)
    (h : ∀ p ∈ S, p.Prime ∧ 2 ^ l ≤ p ∧ Collision p n (2 ^ k)) :
    l * S.card ≤ k * (n * (2 ^ k).choose 2) := by
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  simp only [pow_mul]
  simpa only [pow_mul] using exceptional_prime_power_bound hn S h

/-- Production order and rational heights up to 2^40. Every prime at least 2^158
with a collision consumes a factor in one fixed positive integer. -/
theorem production_height_exception_count (S : Finset ℕ)
    (h : ∀ p ∈ S, p.Prime ∧ 2 ^ 158 ≤ p ∧ Collision p (2 ^ 30) (2 ^ 40)) :
    32000 * S.card < 2 ^ 122 := by
  have hi := dyadic_mass (n := 2 ^ 30) (l := 158) (k := 40) (by positivity) S h
  rw [Nat.choose_two_right] at hi
  norm_num at hi ⊢
  omega

#print axioms ratio_pow_eq_one_iff
#print axioms exceptional_prime_power_bound
#print axioms production_height_exception_count

end ArkLib.ProximityGap.PrimeFieldMultiplierHeight
