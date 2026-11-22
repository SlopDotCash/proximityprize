/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Packing signed locator vectors after prescribing Fourier coordinates

An upper bound on the squared length and a lower bound on pairwise squared
distance bound the number of distinct vectors. The vectors can be restricted
to the unmarked coordinates when several signed entries have been fixed.
-/
namespace ProximityGap.LocatorSignedPacking

open Finset

variable {ι α : Type*} [Fintype ι] [Fintype α]

private theorem coord_distance_sum (z : ι → ℤ) :
    ∑ i, ∑ j, (z i - z j) ^ 2 =
      2 * Fintype.card ι * (∑ i, z i ^ 2) - 2 * (∑ i, z i) ^ 2 := by
  classical
  simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  simp [← sum_mul, ← mul_sum, sq]
  ring

/-- Pairwise Euclidean separation and a squared length cap give the Plotkin count.
The result is written without division to include all integer inputs. -/
theorem signed_packing [Nonempty ι] (w : ι → α → ℤ) (s u : ℤ)
    (hsize : ∀ i, ∑ k, (w i k) ^ 2 ≤ u)
    (hsep : ∀ i j, i ≠ j → s ≤ ∑ k, (w i k - w j k) ^ 2) :
    (Fintype.card ι : ℤ) * (s - 2 * u) ≤ s := by
  classical
  let L : ℤ := Fintype.card ι
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hlo (i : ι) : (L - 1) * s ≤ ∑ j, ∑ k, (w i k - w j k) ^ 2 := by
    calc
      _ = ∑ _j ∈ univ.erase i, s := by
        rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, nsmul_eq_mul]
        simp [L, Nat.cast_sub (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card ι))]
      _ ≤ ∑ j ∈ univ.erase i, ∑ k, (w i k - w j k) ^ 2 :=
        sum_le_sum (fun j hj => hsep i j (Ne.symm (mem_erase.mp hj).1))
      _ = _ := by
        rw [← add_sum_erase univ (fun j => ∑ k, (w i k - w j k) ^ 2) (mem_univ i)]
        simp
  have hsum : L * ((L - 1) * s) ≤ ∑ i, ∑ j, ∑ k, (w i k - w j k) ^ 2 := by
    simpa [L] using sum_le_sum (s := (univ : Finset ι)) (fun i _ => hlo i)
  have hcoord (k : α) : ∑ i, ∑ j, (w i k - w j k) ^ 2 ≤
      (2 * L) * ∑ i, w i k ^ 2 := by
    rw [coord_distance_sum (fun i => w i k)]
    nlinarith [sq_nonneg (∑ i, w i k)]
  have hi : ∑ i, ∑ j, ∑ k, (w i k - w j k) ^ 2 ≤ 2 * L * (L * u) := by
    calc
      _ = ∑ k, ∑ i, ∑ j, (w i k - w j k) ^ 2 := by
        conv_lhs => arg 2; ext i; rw [sum_comm]
        rw [sum_comm]
      _ ≤ ∑ k, (2 * L) * ∑ i, w i k ^ 2 := sum_le_sum (fun k _ => hcoord k)
      _ = (2 * L) * ∑ i, ∑ k, w i k ^ 2 := by rw [← mul_sum, sum_comm]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [L] using sum_le_sum (s := (univ : Finset ι)) (fun i _ => hsize i)
  change L * (s - 2 * u) ≤ s
  apply le_of_mul_le_mul_left (a := L) _ hL
  nlinarith only [hsum.trans hi]

/-- For two layers whose coordinate sums agree modulo two, squared distance is even.
An odd lower bound for that distance can therefore be increased by one. -/
theorem even_distance_lower_bound (z w : α → ℤ) (l : ℤ)
    (hpar : (2 : ℤ) ∣ (∑ i, z i) - ∑ i, w i)
    (h : 2 * l + 1 ≤ ∑ i, (z i - w i) ^ 2) :
    2 * l + 2 ≤ ∑ i, (z i - w i) ^ 2 := by
  have hd : (2 : ℤ) ∣ ∑ i, ((z i - w i) ^ 2 - (z i - w i)) := by
    apply dvd_sum
    intro i _
    simpa only [sq, mul_sub, mul_one] using (Int.even_mul_pred_self (z i - w i)).two_dvd
  simp only [sum_sub_distrib] at hd
  have he := dvd_add hd hpar
  rw [sub_add_cancel] at he
  obtain ⟨j, hj⟩ := he
  omega

#print axioms even_distance_lower_bound
#print axioms signed_packing

end ProximityGap.LocatorSignedPacking
