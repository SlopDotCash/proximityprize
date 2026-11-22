/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # A cubic distance bound for 510-bit locator supports

The off-diagonal part of the square of a binary Gram kernel is itself a Gram
kernel. Multiplying it by the original kernel gives the required third-moment
inequality, without numerical eigenvalue estimates.
-/

namespace ProximityGap.LocatorBinaryCubic
open Finset
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

/-- Inner product of two feature vectors indexed by the codewords. -/
def gram (u : α → ι → ℤ) (x y : ι) : ℤ := ∑ i, u i x * u i y

/-- The sum over all pairs of a Gram kernel is a sum of integer squares. -/
theorem gram_sum_nonneg (u : α → ι → ℤ) :
    0 ≤ ∑ x, ∑ y, gram u x y := by
  unfold gram
  simp_rw [Finset.sum_comm (s := (univ : Finset ι)) (t := (univ : Finset α))]
  apply Finset.sum_nonneg
  intro i _
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  exact mul_self_nonneg _

omit [Fintype ι] in
private theorem gram_mul (u : α → ι → ℤ) (v : β → ι → ℤ) (x y : ι) :
    gram u x y * gram v x y = gram (fun p : α × β => fun z => u p.1 z * v p.2 z) x y := by
  simp only [gram, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm (s := (univ : Finset β)) (t := (univ : Finset α))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The off-diagonal quadratic features, with the diagonal explicitly set to zero. -/
def off (u : α → ι → ℤ) [DecidableEq α] (p : α × α) (x : ι) : ℤ :=
  if p.1 = p.2 then 0 else u p.1 x * u p.2 x

omit [Fintype ι] in
private theorem square_split (u : α → ι → ℤ) (hu : ∀ i x, (u i x) ^ 2 = 1)
    [DecidableEq α] (x y : ι) :
    (gram u x y) ^ 2 = gram (off u) x y + Fintype.card α := by
  rw [pow_two, gram_mul]
  unfold gram
  simp only [Fintype.sum_prod_type]
  have diag (i j : α) :
      (u i x * u j x) * (u i y * u j y) =
        off u (i,j) x * off u (i,j) y + (if j = i then 1 else 0) := by
    by_cases h : j = i
    · subst j
      simp only [off, ite_true, mul_zero, zero_add]
      rw [← pow_two, ← pow_two, hu, hu]
      norm_num
    · simp [off,h,Ne.symm h]
  simp_rw [diag, Finset.sum_add_distrib]
  simp

/-- On 510 coordinates, a family with all distinct pairs of inner product at
most 22 has at most 230,291 members. Each feature is a sign. -/
theorem cubic_bound (u : Fin 510 → ι → ℤ) (hu : ∀ i x, (u i x) ^ 2 = 1)
    (hpair : ∀ x y, x ≠ y → gram u x y ≤ 22) : Fintype.card ι ≤ 230291 := by
  classical
  let g := gram u
  let b := gram (off u)
  have hs (x y : ι) : g x y ^ 2 = b x y + 510 := by
    simpa [g,b] using square_split u hu x y
  have hb : 0 ≤ ∑ x, ∑ y, b x y := gram_sum_nonneg _
  have hg : 0 ≤ ∑ x, ∑ y, g x y := gram_sum_nonneg _
  have hbg : 0 ≤ ∑ x, ∑ y, g x y * b x y := by
    simp only [g,b,gram_mul]
    exact gram_sum_nonneg _
  let f (t : ℤ) := (t-22)*(t+23) ^ 2
  have expand (x y : ι) :
      f (g x y) = g x y * b x y + 27 * g x y + 24*b x y + 602 := by
    dsimp [f]
    linear_combination (g x y + 24) * hs x y
  have lower : 602*(Fintype.card ι : ℤ) ^ 2 ≤ ∑ x, ∑ y, f (g x y) := by
    simp_rw [expand, Finset.sum_add_distrib]
    simp only [← Finset.mul_sum, sum_const, card_univ, nsmul_eq_mul]
    nlinarith
  have diag (x : ι) : g x x = 510 := by
    unfold g gram
    simp only [← pow_two, hu, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have upper : (∑ x, ∑ y, f (g x y)) ≤ (Fintype.card ι : ℤ)*138635432 := by
    calc
      _ ≤ ∑ x : ι, ∑ y : ι, if x = y then (138635432:ℤ) else 0 := by
        gcongr with x _ y _
        split_ifs with h
        · subst y
          rw [diag]; decide
        · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hpair x y h)) (sq_nonneg _)
      _ = _ := by simp
  have h := lower.trans upper
  by_contra! large
  have hlarge : (230292 : ℤ) ≤ Fintype.card ι := by exact_mod_cast large
  nlinarith

#print axioms cubic_bound
end ProximityGap.LocatorBinaryCubic
