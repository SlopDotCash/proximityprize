/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.Errors
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination

/-!
# Affine list recovery and quadratic Paley discrepancy

The affine Reed–Solomon words are the shifts `x ↦ x + b` on a prescribed set
`A`. Each coordinate accepts every nonzero square (or every nonsquare).
A positive excess of agreements above half the domain contributes positive
(or negative) Paley discrepancy. The possible zero symbol gets its own
diagonal correction. All list sizes below count field shifts.
-/

namespace ProximityGap.PaleyShiftListRecovery

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The number of coordinates where the affine word hits the symbol list of sign `s`. -/
def agreements (A : Finset F) (b : F) (s : ℤ) : ℕ :=
  (A.filter fun x => quadraticChar F (x + b) = s).card

/-- Shifts exceeding a specified signed agreement excess. -/
def shiftList (A : Finset F) (s t : ℤ) : Finset F :=
  univ.filter fun b => t < 2 * (agreements A b s : ℤ) - A.card + (if -b ∈ A then 1 else 0)

/-- Exact conversion from list-recovery agreements to a shifted character sum. -/
theorem agreement_excess (A : Finset F) (b : F) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    s * (∑ x ∈ A, quadraticChar F (x + b)) =
      2 * (agreements A b s : ℤ) - A.card + (if -b ∈ A then 1 else 0) := by
  have hterm (x : F) : s * quadraticChar F (x + b) =
      2 * (if quadraticChar F (x + b) = s then 1 else 0) - 1 +
        (if x = -b then 1 else 0) := by
    by_cases hx : x + b = 0
    · have he := eq_neg_of_add_eq_zero_left hx
      rcases hs with rfl | rfl <;> simp [he]
    · have he : x ≠ -b := fun h => hx (by simp [h])
      rcases quadraticChar_dichotomy hx with h | h <;> rcases hs with rfl | rfl <;> simp [h, he]
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [agreements]

private theorem signed_sum_bound (A B : Finset F) {s t : ℤ} (hs : s = 1 ∨ s = -1)
    (ht : 0 ≤ t) :
    s * (∑ b ∈ B, ∑ x ∈ A, quadraticChar F (x + b)) ≤
      B.card * t + A.card * ((shiftList A s t).card : ℤ) := by
  classical
  have hpoint (b : F) : s * (∑ x ∈ A, quadraticChar F (x + b)) ≤
      t + (if b ∈ shiftList A s t then (A.card : ℤ) else 0) := by
    by_cases hb : b ∈ shiftList A s t
    · simp only [hb, ite_true]
      calc
        _ = ∑ x ∈ A, s * quadraticChar F (x + b) := Finset.mul_sum ..
        _ ≤ ∑ _x ∈ A, (1 : ℤ) := by
          apply Finset.sum_le_sum
          intro x _
          by_cases h : x + b = 0
          · simp [h]
          · rcases quadraticChar_dichotomy h with h | h <;> rcases hs with rfl | rfl <;> simp [h]
        _ ≤ _ := by simp; omega
    · simp only [hb, ↓reduceIte, add_zero]
      rw [agreement_excess A b hs]
      simpa [shiftList] using hb
  have hcount : (B ∩ shiftList A s t).card ≤ (shiftList A s t).card :=
    Finset.card_le_card Finset.inter_subset_right
  rw [Finset.mul_sum]
  calc
    _ ≤ _ := Finset.sum_le_sum (fun b (_ : b ∈ B) => hpoint b)
    _ = B.card * t + (B ∩ shiftList A s t).card * (A.card : ℤ) := by
      simp [Finset.sum_add_distrib]
    _ ≤ _ := by rw [mul_comm (A.card : ℤ)]; gcongr

/-- A bound for both lists of affine words gives discrepancy for every test set `B`. -/
theorem discrepancy_of_list_bounds (A B : Finset F) {t : ℤ} (ht : 0 ≤ t) (L : ℕ)
    (hL : ∀ s : ℤ, s = 1 ∨ s = -1 → (shiftList A s t).card ≤ L) :
    |∑ b ∈ B, ∑ x ∈ A, quadraticChar F (x + b)| ≤ B.card * t + A.card * (L : ℤ) := by
  have h (s : ℤ) (hs : s = 1 ∨ s = -1) := (signed_sum_bound A B hs ht).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr (hL s hs))
      (Int.natCast_nonneg A.card)) _)
  have hp := h 1 (Or.inl rfl)
  have hn := h (-1) (Or.inr rfl)
  rw [abs_le]
  simp only [one_mul, neg_one_mul] at hp hn
  omega

/-- Uniform discrepancy at size `m` and above rules out `m` exceptional shifts of either sign. -/
theorem list_bound_of_discrepancy (A : Finset F) {m : ℕ} (hm : 0 < m) (t : ℤ)
    (h : ∀ B : Finset F, m ≤ B.card →
      |∑ b ∈ B, ∑ x ∈ A, quadraticChar F (x + b)| ≤ B.card * t)
    {s : ℤ} (hs : s = 1 ∨ s = -1) : (shiftList A s t).card < m := by
  by_contra! hlarge
  let B := shiftList A s t
  have hlt : (∑ _b ∈ B, t) < ∑ b ∈ B, s * (∑ x ∈ A, quadraticChar F (x + b)) := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (hm.trans_le hlarge))
    intro b hb
    rw [agreement_excess A b hs]
    exact (Finset.mem_filter.mp hb).2
  rw [← Finset.mul_sum] at hlt
  have hb := abs_le.mp (h B hlarge)
  rcases hs with rfl | rfl <;>
    simp only [Finset.sum_const, nsmul_eq_mul, one_mul, neg_one_mul] at hlt <;> omega

/-- Against one ordinary received word, each coordinate agrees with exactly one shift. -/
theorem singleton_center_total (A : Finset F) (y : F → F) :
    ∑ b : F, (A.filter (fun x => x + b = y x)).card = A.card := by
  have he (x b : F) : y x - x = b ↔ x + b = y x := by
    constructor <;> intro h <;> linear_combination -h
  simpa only [he, mem_univ, filter_true] using
    sum_card_fiberwise_eq_card_filter A univ (fun x => y x - x)

/-- If symbol lists can vary with the coordinate, translating one set `S` at
each coordinate makes every shift in `S` agree everywhere. -/
theorem translated_symbol_lists (A S : Finset F) (b : F) :
    (A.filter (fun x => x + b ∈ S.image (x + ·))).card = if b ∈ S then A.card else 0 := by
  classical
  have he (x : F) : x + b ∈ S.image (x + ·) ↔ b ∈ S := by simp
  by_cases hb : b ∈ S <;> simp [he, hb]

/-- The same affine shifts arise by folding the coordinate row and the constant row.
Both rows have joint witnesses in every Reed–Solomon dimension at least two. -/
theorem affine_shift_mca_clean {K I : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [Nonempty I] [DecidableEq I] (D : I ↪ K) {k : ℕ} (hk : 2 ≤ k)
    (δ : NNReal) (b : K) :
    ¬ mcaEvent (ReedSolomon.code D k : Set (I → K)) δ D (fun _ => 1) b := by
  rintro ⟨S, _, _, hno⟩
  apply hno
  refine ⟨D, ?_, (fun _ => 1), ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  · exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval Polynomial.X
      (by simp; omega) (by simp)
  · exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval 1
      (by simp; omega) (by simp)

#print axioms singleton_center_total
#print axioms translated_symbol_lists
#print axioms affine_shift_mca_clean
#print axioms agreement_excess
#print axioms discrepancy_of_list_bounds
#print axioms list_bound_of_discrepancy

end ProximityGap.PaleyShiftListRecovery
