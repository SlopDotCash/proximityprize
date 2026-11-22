/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyInversionTrace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

/-! # Local fourth moments for Paley matrices on one product stratum -/

namespace ProximityGap.PaleyProductStratumNorm

open Finset

section Cyclic

variable {m : ℕ} [NeZero m]
local notation "C" => ZMod (2*m)

/-- Lifted kernel after removing the row sign of absolute value one. -/
def matrix (h : C → ℤ) (e i j : C) := h (i-j) * h (i+j-e)

/-- The row-sign product along a parallelogram of prescribed steps. -/
def four (h : C → ℤ) (a b r : C) := h r * h (r+a) * h (r+b) * h (r+a+b)

omit [NeZero m] in
private theorem rectangle (h : C → ℤ) (e a b i j : C) :
    matrix h e i j * matrix h e (i+a) j * matrix h e (i+a) (j+b) * matrix h e i (j+b) =
      four h a (-b) (i-j) * four h a b (i+j-e) := by
  unfold matrix four
  have h₁ : i+a-j=i-j+a := by abel
  have h₂ : i+a+j-e=i+j-e+a := by abel
  have h₃ : i+a-(j+b)=i-j+a+ -b := by abel
  have h₄ : i+a+(j+b)-e=i+j-e+a+b := by abel
  have h₅ : i-(j+b)=i-j+ -b := by abel
  have h₆ : i+(j+b)-e=i+j-e+b := by abel
  rw [h₁,h₂,h₃,h₄,h₅,h₆]
  ring

/-- The sum over all corners of a fixed shape reduces to two parity-restricted
products of one-dimensional four-point correlations. -/
theorem rectangle_sum (h : C → ℤ) (e a b : C) :
    (∑ z : C × C, matrix h e z.1 z.2 * matrix h e (z.1+a) z.2 *
      matrix h e (z.1+a) (z.2+b) * matrix h e z.1 (z.2+b)) =
      ∑ z : C × C, if z.1.val%2=z.2.val%2 then
        2*(four h a (-b) z.1 * four h a b (z.2-e)) else 0 := by
  simp_rw [rectangle]
  simpa only [two_mul] using PaleyInversionTrace.sum_difference_pushforward
    (m:=m) (fun z => four h a (-b) z.1 * four h a b (z.2-e))

end Cyclic

section Gram

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The fourth power of a block bilinear form is bounded by the squared row
inner products and the fourth powers of the two vector norms. -/
theorem block_fourth (A : I → J → ℝ) (u : I → ℝ) (v : J → ℝ) :
    (∑ j, v j * ∑ i, u i * A i j)^4 ≤
      (∑ i, (u i)^2)^2 * (∑ j, (v j)^2)^2 *
        ∑ z : I × I, (∑ j, A z.1 j * A z.2 j)^2 := by
  classical
  let G (z : I × I) := ∑ j, A z.1 j*A z.2 j
  let w (z : I × I) := u z.1*u z.2
  have hg : (∑ j, (∑ i, u i*A i j)^2) = ∑ z, w z * G z := by
    simp only [G,w,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul,pow_two]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro j _
    ring
  have hw : ∑ z, (w z)^2 = (∑ i, (u i)^2)^2 := by
    simp only [w,Fintype.sum_prod_type,pow_two,sum_mul,mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro k _
    ring
  have h := sum_mul_sq_le_sq_mul_sq univ v (fun j => ∑ i, u i*A i j)
  have h' := sum_mul_sq_le_sq_mul_sq univ w G
  rw [hw,← hg] at h'
  calc
    _ = ((∑ j, v j * ∑ i, u i * A i j)^2)^2 := by ring
    _ ≤ ((∑ j, (v j)^2) * ∑ j, (∑ i, u i*A i j)^2)^2 :=
      pow_le_pow_left₀ (sq_nonneg _) h 2
    _ ≤ (∑ j, (v j)^2)^2 * ((∑ i, (u i)^2)^2 * ∑ z, (G z)^2) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left h' (sq_nonneg _)
    _ = _ := by unfold G; ring

/-- Combining the block norms costs the number of blocks in the fourth power.
Here `u` and `v` may be the Euclidean norms of the restricted test vectors. -/
theorem assemble_fourth (K : I × J → ℝ) (u : I → ℝ) (v : J → ℝ) :
    (∑ z, K z * (u z.1 * v z.2))^4 ≤
      (Fintype.card (I × J) : ℝ) * (∑ z, (K z)^4) *
        (∑ i, (u i)^2)^2 * (∑ j, (v j)^2)^2 := by
  classical
  let w (z : I × J) := u z.1 * v z.2
  have hw : ∑ z, (w z)^2 = (∑ i, (u i)^2) * ∑ j, (v j)^2 := by
    simp only [w,Fintype.sum_prod_type,mul_pow,sum_mul,mul_sum]
    rw [sum_comm]
  have hc := sum_mul_sq_le_sq_mul_sq univ (fun _ : I × J => (1:ℝ)) (fun z => (K z)^2)
  simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one,← pow_mul] at hc
  have h := sum_mul_sq_le_sq_mul_sq univ K w
  rw [hw] at h
  calc
    _ = ((∑ z, K z*w z)^2)^2 := by ring
    _ ≤ ((∑ z, (K z)^2)*((∑ i, (u i)^2)*∑ j, (v j)^2))^2 :=
      pow_le_pow_left₀ (sq_nonneg _) h 2
    _ ≤ ((Fintype.card (I × J) : ℝ)*(∑ z, (K z)^4)) *
        ((∑ i, (u i)^2)*∑ j, (v j)^2)^2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by ring

/-- A separate bound on the row norms removes the Gram diagonal from the
fourth moment. The remaining squared entries determine the error in the
quadratic form. -/
theorem gram_diagonal (G : I → I → ℝ) [DecidableEq I] (D L : ℝ) (hL : 0 ≤ L)
    (hd : ∀ i, G i i ≤ D)
    (he : ∑ z : I × I, (if z.1=z.2 then 0 else G z.1 z.2)^2 ≤ L^2) (u : I → ℝ) :
    (∑ z : I × I, (u z.1*u z.2)*G z.1 z.2) ≤ (D+L)*∑ i, (u i)^2 := by
  classical
  let O (z : I × I) : ℝ := if z.1=z.2 then 0 else G z.1 z.2
  let w (z : I × I) := u z.1*u z.2
  let N := ∑ i, (u i)^2
  have hN : 0 ≤ N := sum_nonneg (fun _ _ => sq_nonneg _)
  have hw : ∑ z, (w z)^2 = N^2 := by
    simp only [N,w,Fintype.sum_prod_type,pow_two,sum_mul,mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro k _
    ring
  have hoff : ∑ z, w z*O z ≤ N*L := by
    apply le_trans (le_abs_self _)
    apply le_of_sq_le_sq _ (mul_nonneg hN hL)
    rw [sq_abs,mul_pow]
    apply (sum_mul_sq_le_sq_mul_sq univ w O).trans
    rw [hw]
    exact mul_le_mul_of_nonneg_left he (sq_nonneg N)
  have hdecomp : (∑ z : I × I, (u z.1*u z.2)*G z.1 z.2) =
      ∑ i, (u i)^2*G i i + ∑ z, w z*O z := by
    have hpoint (z : I × I) : (u z.1*u z.2)*G z.1 z.2 =
        (if z.2=z.1 then (u z.1)^2*G z.1 z.1 else 0) + w z*O z := by
      rcases z with ⟨i,j⟩
      by_cases hh : i=j
      · subst j
        simp [w,O,pow_two]
      · simp [w,O,hh,Ne.symm hh]
    simp_rw [hpoint,sum_add_distrib]
    congr 1
    rw [Fintype.sum_prod_type]
    simp
  rw [hdecomp,add_mul]
  apply add_le_add _ (by simpa [mul_comm] using hoff)
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (hd i) (sq_nonneg (u i))

end Gram

end ProximityGap.PaleyProductStratumNorm

#print axioms ProximityGap.PaleyProductStratumNorm.rectangle_sum
#print axioms ProximityGap.PaleyProductStratumNorm.block_fourth
#print axioms ProximityGap.PaleyProductStratumNorm.assemble_fourth

#print axioms ProximityGap.PaleyProductStratumNorm.gram_diagonal
