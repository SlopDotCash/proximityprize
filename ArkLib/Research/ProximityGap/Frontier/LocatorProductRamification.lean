/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Int.ModEq
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring

/-!
# Double divisibility from a prescribed root product

An integer polynomial vanishing at one with even derivative there gains a
second factor of `z - 1` in every commutative ring where `z ^ n = -1`.
For equal-size cyclic supports, equality of their exponent sums modulo an
even group order supplies the derivative condition.
-/

namespace ProximityGap.LocatorProductRamification

open Polynomial
open scoped Polynomial

variable {R : Type*} [CommRing R]

/-- Taylor expansion through degree one controls the divisibility of the value
at a second point. The argument also holds in rings with zero divisors. -/
theorem sq_dvd_eval {F : R[X]} {a z : R} (hF : F.eval a = 0)
    (hd : z - a ∣ F.derivative.eval a) : (z - a) ^ 2 ∣ F.eval z := by
  obtain ⟨c, ht⟩ := F.exists_mul_sq_add_linear_part_eq_eval_add a (z - a)
  obtain ⟨d, hd⟩ := hd
  rw [hd, hF, show a + (z - a) = z by ring] at ht
  refine ⟨c + d, ?_⟩
  rw [← ht]
  ring

/-- An even integer derivative supplies the second factor whenever `z - 1 ∣ 2`. -/
theorem sq_dvd_eval₂_int {F : ℤ[X]} {z : R} (hF : F.eval 1 = 0)
    (hd : (2 : ℤ) ∣ F.derivative.eval 1) (hz : z - 1 ∣ (2 : R)) :
    (z - 1) ^ 2 ∣ F.eval₂ (Int.castRingHom R) z := by
  rw [Polynomial.eval₂_eq_eval_map]
  apply sq_dvd_eval (a := 1)
  · simp [Polynomial.eval_map, Polynomial.eval₂_at_one, hF]
  · rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_one]
    obtain ⟨c, hc⟩ := hd
    exact hz.trans ⟨(c : R), by simp [hc]⟩

/-- At any root of `X^n + 1`, the element `z - 1` divides two. -/
theorem sub_one_dvd_two {z : R} {n : ℕ} (hz : z ^ n = -1) : z - 1 ∣ (2 : R) := by
  have h := (sub_one_dvd_pow_sub_one z n).neg_right
  rwa [hz, show -(-1 - 1 : R) = 2 by ring] at h

/-- Double divisibility at a root of a dyadic cyclotomic polynomial, in any
target ring. The exponent need not itself be a power of two. -/
theorem sq_dvd_eval₂_int_of_pow_eq_neg_one {F : ℤ[X]} {z : R} {n : ℕ}
    (hF : F.eval 1 = 0) (hd : (2 : ℤ) ∣ F.derivative.eval 1) (hz : z ^ n = -1) :
    (z - 1) ^ 2 ∣ F.eval₂ (Int.castRingHom R) z :=
  sq_dvd_eval₂_int hF hd (sub_one_dvd_two hz)

/-- Equal-size exponent supports with a common exponent sum modulo an even
order give the required double divisor at every root of `X^n + 1`. -/
theorem sq_dvd_sub_sum_pow (S T : Finset ℕ) {m : ℤ} {n : ℕ} {z : R}
    (hcard : S.card = T.card) (hm : 2 ∣ m)
    (hsum : (∑ j ∈ S, (j : ℤ)) ≡ (∑ j ∈ T, (j : ℤ)) [ZMOD m]) (hz : z ^ n = -1) :
    (z - 1) ^ 2 ∣ (∑ j ∈ S, z ^ j) - ∑ j ∈ T, z ^ j := by
  let F : ℤ[X] := (∑ j ∈ S, X ^ j) - ∑ j ∈ T, X ^ j
  have hF : F.eval 1 = 0 := by
    simp [F, Polynomial.eval_finsetSum, hcard]
  have hd : (2 : ℤ) ∣ F.derivative.eval 1 := by
    simpa [F, Polynomial.derivative_sum, Polynomial.derivative_X_pow, Polynomial.eval_finsetSum]
      using hm.trans (Int.modEq_iff_dvd.mp hsum.symm)
  simpa [F, Polynomial.eval₂_finsetSum] using sq_dvd_eval₂_int_of_pow_eq_neg_one hF hd hz

/-- Fixed products in one cyclic group force the square divisor when the signed
support sum is evaluated in another ring. This is the form used for locators:
the product can be prescribed in the prime field before lifting to characteristic zero. -/
theorem sq_dvd_sub_sum_pow_of_prod_eq {G : Type*} [CommGroup G] (g : G)
    (S T : Finset ℕ) {n : ℕ} {z : R} (hcard : S.card = T.card) (hm : 2 ∣ orderOf g)
    (hprod : (∏ j ∈ S, g ^ j) = ∏ j ∈ T, g ^ j) (hz : z ^ n = -1) :
    (z - 1) ^ 2 ∣ (∑ j ∈ S, z ^ j) - ∑ j ∈ T, z ^ j := by
  have hp : g ^ (∑ j ∈ S, j) = g ^ (∑ j ∈ T, j) := by
    rw [← Finset.prod_pow_eq_pow_sum S (fun j => j) g,
      ← Finset.prod_pow_eq_pow_sum T (fun j => j) g]
    exact hprod
  apply sq_dvd_sub_sum_pow S T (m := (orderOf g : ℤ)) hcard _ _ hz
  · exact_mod_cast hm
  · simpa using Int.natCast_modEq_iff.mpr (pow_eq_pow_iff_modEq.mp hp)

/-- Any multiplicative integer norm sends this square divisor to a multiple of
four if the norm of its base is even. -/
theorem four_dvd_norm_of_sq_dvd (N : R →* ℤ) {d v : R} (hN : (2 : ℤ) ∣ N d)
    (hv : d ^ 2 ∣ v) : (4 : ℤ) ∣ N v := by
  obtain ⟨c, hc⟩ := hN
  obtain ⟨w, hw⟩ := hv
  refine ⟨c ^ 2 * N w, ?_⟩
  rw [hw, map_mul, map_pow, hc]
  ring

#print axioms sq_dvd_eval
#print axioms sq_dvd_eval₂_int_of_pow_eq_neg_one
#print axioms sq_dvd_sub_sum_pow
#print axioms sq_dvd_sub_sum_pow_of_prod_eq
#print axioms four_dvd_norm_of_sq_dvd

end ProximityGap.LocatorProductRamification
