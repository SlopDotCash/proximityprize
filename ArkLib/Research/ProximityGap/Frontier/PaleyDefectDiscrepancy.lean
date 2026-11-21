/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyShiftListRecovery
import Mathlib.Algebra.Order.Chebyshev

/-! # From signed defect multiplicities to quadratic discrepancy

The positive part of the defect at each shift determines a nonnegative upper bound
on the signed row sum plus its zero entry. Squaring that upper bound gives the
charge in the determinant degree estimate, up to a constant shared by every row.
-/

namespace ProximityGap.PaleyDefectDiscrepancy

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Number of symbols of the opposite sign at the specified shift. -/
def defects (A : Finset F) (σ : ℤ) (b : F) : ℕ :=
  (A.filter fun u => quadraticChar F (b + u) = -σ).card

/-- Multiplicity supplied by a row having `e` defects. Both subtractions truncate at zero. -/
def charge (a x e : ℕ) : ℕ := (x - e) * (a - x - e)

private theorem clamp_sq (a x e : ℕ) (hx : 2*x ≤ a) :
    (a - 2*x + 2*(x-e))^2 = (a - 2*x)^2 + 4*charge a x e := by
  unfold charge
  by_cases he : e ≤ x
  · rw [show a-x-e = (a-2*x)+(x-e) by omega]
    ring
  · simp [Nat.sub_eq_zero_of_le (show x ≤ e by omega)]

/-- Cauchy converts a bound on the total charge into a squared bound for clipped row sums. -/
theorem clamp_sum_sq {I : Type*} (B : Finset I) (e : I → ℕ) {a x N : ℕ} (hx : 2*x ≤ a)
    (hbudget : ∑ b ∈ B, charge a x (e b) ≤ N) :
    (∑ b ∈ B, (a - 2*x + 2*(x-e b)))^2 ≤ B.card^2 * (a-2*x)^2 + 4*B.card*N := by
  have h := sq_sum_le_card_mul_sum_sq (s := B) (f := fun b => a - 2*x + 2*(x-e b))
  refine h.trans ?_
  simp only [clamp_sq _ _ _ hx, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum,
    Nat.cast_id]
  nlinarith only [Nat.mul_le_mul_left (4*B.card) hbudget]

/-- On an actual quadratic-character rectangle, charge bounds for the two signs give
the squared discrepancy bound including one unit per zero symbol. -/
theorem discrepancy_sq_of_budgets (A B : Finset F) (x N : ℕ) (hx : 2*x ≤ A.card)
    (hbudget : ∀ σ : ℤ, σ = 1 ∨ σ = -1 → ∑ b ∈ B, charge A.card x (defects A σ b) ≤ N) :
    (|∑ b ∈ B, ∑ u ∈ A, quadraticChar F (b+u)| + ((B.filter fun b => -b ∈ A).card : ℤ))^2 ≤
      (B.card : ℤ)^2 * ((A.card : ℤ) - 2*x)^2 + 4*B.card*N := by
  let W (b : F) := ∑ u ∈ A, quadraticChar F (b+u)
  let S := ∑ b ∈ B, W b
  let Z := (B.filter fun b => -b ∈ A).card
  let σ : ℤ := if 0 ≤ S then 1 else -1
  have hs : σ = 1 ∨ σ = -1 := by dsimp [σ]; split <;> simp
  have hsabs : σ*S = |S| := by
    dsimp [σ]
    split <;> rename_i h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  let Q (b : F) := A.card - 2*x + 2*(x-defects A σ b)
  have hrow (b : F) : σ * W b + (if -b ∈ A then (1:ℤ) else 0) ≤ Q b := by
    have hneg : -σ = 1 ∨ -σ = -1 := by rcases hs with h | h <;> simp [h]
    have he := PaleyShiftListRecovery.agreement_excess A b hneg
    have hd : PaleyShiftListRecovery.agreements A b (-σ) = defects A σ b := by
      simp only [PaleyShiftListRecovery.agreements, defects, add_comm b]
    have hw : (∑ u ∈ A, quadraticChar F (u+b)) = W b := by simp only [W, add_comm b]
    rw [hd, neg_mul, hw] at he
    dsimp only [Q]
    omega
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ B) => hrow b)
  rw [sum_add_distrib, ← mul_sum, sum_boole] at hsum
  change σ*S + (Z : ℤ) ≤ ∑ b ∈ B, (Q b : ℤ) at hsum
  rw [hsabs] at hsum
  have hN := clamp_sum_sq B (defects A σ) hx (hbudget σ hs)
  change (∑ b ∈ B, Q b)^2 ≤ _ at hN
  have hbound : ((∑ b ∈ B, Q b) : ℤ)^2 ≤
      (B.card : ℤ)^2 * ((A.card-2*x : ℕ) : ℤ)^2 + 4*B.card*N := by exact_mod_cast hN
  rw [Nat.cast_sub hx, Nat.cast_mul, Nat.cast_ofNat] at hbound
  change (|S| + (Z : ℤ))^2 ≤ _
  refine (pow_le_pow_left₀ (add_nonneg (abs_nonneg S) (Int.natCast_nonneg Z)) hsum 2).trans ?_
  exact hbound

#print axioms clamp_sum_sq
#print axioms discrepancy_sq_of_budgets

end ProximityGap.PaleyDefectDiscrepancy
