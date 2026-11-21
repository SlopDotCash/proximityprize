/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib

/-! # The lattice step behind the section-incidence bound

A symmetric bilinear form that is nonpositive on the orthogonal complement of a
fibre class satisfies a Bessel inequality for one section against pairwise
orthogonal fibre components. Every intersection number is a hypothesis. The
surface on which these numbers hold is constructed in
`docs/research/proximity-gap/section-incidence-hodge-index.md`.

The file also checks the counting step for totally ramified core sites, the
packing step and integer values of the tangent-head bound, and the integer
values of the weight-free population bound.
-/

set_option autoImplicit false

namespace ProximityGap.HodgeSectionLattice

open Finset

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Cauchy–Schwarz for a symmetric bilinear form that is nonpositive on the span
of two vectors. -/
theorem sq_le_mul_of_nonpos (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ u v, B u v = B v u)
    (T C : V) (hneg : ∀ r s : ℝ, B (r • T + s • C) (r • T + s • C) ≤ 0) :
    (B T C) ^ 2 ≤ B T T * B C C := by
  have expand : ∀ r s : ℝ, B (r • T + s • C) (r • T + s • C)
      = r ^ 2 * B T T + 2 * r * s * B T C + s ^ 2 * B C C := by
    intro r s
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hsymm C T]
    ring
  have hCC : B C C ≤ 0 := by
    have h := hneg 0 1
    rw [expand] at h
    linarith
  rcases eq_or_lt_of_le hCC with h0 | hlt
  · have hTC : B T C = 0 := by
      by_contra hne
      have h1 := hneg 1 ((1 - B T T) / (2 * B T C))
      rw [expand, h0] at h1
      have h2 : 2 * 1 * ((1 - B T T) / (2 * B T C)) * B T C = 1 - B T T := by
        field_simp
      nlinarith [h1, h2]
    rw [hTC, h0]
    simp
  · have key := hneg (B C C) (-(B T C))
    rw [expand] at key
    have hprod : B C C * (B C C * B T T - (B T C) ^ 2) ≤ 0 := by nlinarith [key]
    by_contra hcon
    push_neg at hcon
    have hlt2 : B C C * B T T - (B T C) ^ 2 < 0 := by nlinarith [hcon]
    nlinarith [mul_pos_of_neg_of_neg hlt hlt2]

/-- **Lemma 3 of the note.** One section `C` in a fibre of the second fibration,
meeting pairwise orthogonal components `Λ i` of fibres of the first fibration,
satisfies `((b-1)/b · |J|)² ≤ (∑ aᵢ) · c`, where `-aᵢ` are the self-intersections
of the components and `-c` bounds the self-intersection of the section from below. -/
theorem bessel_of_hodge (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ u v, B u v = B v u)
    {Φx Φg C : V} {ι : Type*} [DecidableEq ι] (J : Finset ι) (Λ : ι → V) (a : ι → ℝ)
    {b c : ℝ} (hb : 1 ≤ b)
    (hodge : ∀ T : V, B T Φg = 0 → B T T ≤ 0)
    (hxx : B Φx Φx = 0) (hxg : B Φx Φg = b)
    (hΛx : ∀ i ∈ J, B (Λ i) Φx = 0) (hΛg : ∀ i ∈ J, B (Λ i) Φg = 1)
    (hΛΛ : ∀ i ∈ J, B (Λ i) (Λ i) = -a i)
    (horth : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → B (Λ i) (Λ j) = 0)
    (hCg : B C Φg = 0) (hCx : B C Φx = 1) (hCC : -c ≤ B C C)
    (hinc : ∀ i ∈ J, 1 ≤ B (Λ i) C) :
    ((b - 1) / b * J.card) ^ 2 ≤ (∑ i ∈ J, a i) * c := by
  have hb0 : b ≠ 0 := by positivity
  set m : ℝ := (J.card : ℝ) with hm
  set S : V := ∑ i ∈ J, Λ i with hS
  have sumL : ∀ v, B S v = ∑ i ∈ J, B (Λ i) v := fun v => by
    rw [hS, map_sum, LinearMap.sum_apply]
  have sumR : ∀ v, B v S = ∑ i ∈ J, B v (Λ i) := fun v => by rw [hS, map_sum]
  have hSg : B S Φg = m := by
    rw [sumL, sum_congr rfl hΛg, sum_const, nsmul_eq_mul, mul_one]
  have hSx : B S Φx = 0 := by rw [sumL, sum_congr rfl hΛx, sum_const_zero]
  have hSC : m ≤ B S C := by
    rw [sumL]
    calc m = ∑ _i ∈ J, (1 : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ J, B (Λ i) C := sum_le_sum hinc
  have hSS : B S S = -∑ i ∈ J, a i := by
    rw [sumL, ← sum_neg_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [sumR, sum_eq_single i (fun j hj hji => horth i hi j hj (Ne.symm hji))
      (fun h => absurd hi h), hΛΛ i hi]
  set T : V := S - (m / b) • Φx with hT
  have hTg : B T Φg = 0 := by
    rw [hT, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hSg, hxg,
      smul_eq_mul]
    field_simp
    ring
  have hTT : B T T = -∑ i ∈ J, a i := by
    rw [hT]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hsymm Φx S, hSx, hxx, hSS]
    ring
  have hTC : B T C = B S C - m / b := by
    rw [hT, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hsymm Φx C, hCx,
      smul_eq_mul, mul_one]
  have hCS := sq_le_mul_of_nonpos B hsymm T C (fun r s => hodge _ (by
    rw [map_add, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
      LinearMap.smul_apply, hTg, hCg]
    simp))
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hfrac : (b - 1) / b * m = m - m / b := by
    field_simp
  have hlow : 0 ≤ (b - 1) / b * m :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) hm0
  have hle : (b - 1) / b * m ≤ B T C := by rw [hTC, hfrac]; linarith
  have hsum0 : 0 ≤ ∑ i ∈ J, a i := by
    have h := hodge T hTg
    rw [hTT] at h
    linarith
  calc ((b - 1) / b * m) ^ 2 ≤ (B T C) ^ 2 := by nlinarith [hlow, hle]
    _ ≤ B T T * B C C := hCS
    _ = (∑ i ∈ J, a i) * (-(B C C)) := by rw [hTT]; ring
    _ ≤ (∑ i ∈ J, a i) * c := mul_le_mul_of_nonneg_left (by linarith) hsum0

/-- **Counting step of Lemma U.** If the total number of missed totally ramified
sites is at most `g * u` and `u > d`, at most `3 * g * u / (u - d)` sections miss
a third of the surplus `u - d`. -/
theorem card_large_miss_le {ι : Type*} (S : Finset ι) (miss : ι → ℕ) {g u d : ℕ}
    (hud : d < u) (htotal : ∑ i ∈ S, miss i ≤ g * u) :
    (S.filter fun i => u - d ≤ 3 * miss i).card ≤ 3 * g * u / (u - d) := by
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  have h1 : (S.filter fun i => u - d ≤ 3 * miss i).card * (u - d)
      ≤ ∑ i ∈ S.filter (fun i => u - d ≤ 3 * miss i), 3 * miss i := by
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun i hi => (mem_filter.mp hi).2
  have h2 : ∑ i ∈ S.filter (fun i => u - d ≤ 3 * miss i), 3 * miss i
      ≤ ∑ i ∈ S, 3 * miss i :=
    sum_le_sum_of_subset (filter_subset _ _)
  have h3 : ∑ i ∈ S, 3 * miss i = 3 * ∑ i ∈ S, miss i := by rw [mul_sum]
  nlinarith [h1, h2, h3, htotal]

/-- Three subsets of a `u`-set, each missing fewer than a third of `u - d`
elements, have more than `d` common elements. -/
theorem common_card_gt {α : Type*} [DecidableEq α] (U M₁ M₂ M₃ : Finset α) {d : ℕ}
    (h₁ : 3 * M₁.card < U.card - d) (h₂ : 3 * M₂.card < U.card - d)
    (h₃ : 3 * M₃.card < U.card - d) :
    d < (U \ (M₁ ∪ M₂ ∪ M₃)).card := by
  have hunion : (M₁ ∪ M₂ ∪ M₃).card ≤ M₁.card + M₂.card + M₃.card :=
    (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
  have hsdiff := le_card_sdiff (M₁ ∪ M₂ ∪ M₃) U
  omega

/-- Integer form of the bound of Theorem C in the spread case, with the
exceptional-scalar allowance of `HodgeSectionIncidence.populationBound`. -/
def weightFreeBound (n t d b g h a : ℕ) : ℕ :=
  (4 * b - 2) * g + 1 +
    2 * ((h + ((2 * b - 2) * g + 1)) * n
      + 4 * b ^ 2 * (b - 1) * ((2 * b - 2) * g + 1) ^ 2 * ((2 * b - 2) * a + 1)) / (t - d)

/-- The weight-free values at the last second-prime predecessor, for the cubic
and quartic weights certified by the factor reduction. -/
theorem terminal_weightFree :
    weightFreeBound 1073741824 357913943 67108863 3 34 34 290805098 = 10812548 ∧
    weightFreeBound 1073741824 357913943 67108863 4 34 34 302954072 = 100872934 := by
  decide

/-- Packing step of Theorem D: `N` sets of size `s` in an `n`-set whose pairwise
intersections have at most `r` elements satisfy `N * s² ≤ n * (s + (N - 1) * r)`.
The second-moment count is taken as a hypothesis in the form
`(∑ |Aᵢ|)² ≤ n * (∑ |Aᵢ| + N (N-1) r)`. -/
theorem packing_of_second_moment {N s r n total : ℕ} (hsize : total = N * s)
    (hmoment : total ^ 2 ≤ n * (total + N * (N - 1) * r)) :
    N * s ^ 2 ≤ n * (s + (N - 1) * r) := by
  subst hsize
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp
  · have h : N * (N * s ^ 2) ≤ N * (n * (s + (N - 1) * r)) := by
      calc N * (N * s ^ 2) = (N * s) ^ 2 := by ring
        _ ≤ n * (N * s + N * (N - 1) * r) := hmoment
        _ = N * (n * (s + (N - 1) * r)) := by ring
    exact Nat.le_of_mul_le_mul_left h hpos

/-- Integer form of the bound of Theorem D: exceptional scalars, sections of
large height, sections with many degenerate agreements, and `h` sections for
each class of tangent heads. -/
def tangentHeadBound (n t d b g h a W cbar nbar : ℕ) : ℕ :=
  (4 * b - 2) * g + 1
    + (4 * ((2 * b - 2) * g + 1) * ((2 * b - 2) * a + 1)
        + b * (W * (h - b) + h * (W - b * d))) / (cbar + 1)
    + h * n / (nbar + 1)
    + h * (n * (t - nbar - cbar - (d + 2 * cbar))
        / ((t - nbar - cbar) ^ 2 - n * (d + 2 * cbar)))

/-- Theorem D at the last second-prime predecessor: the Johnson-type condition
holds for the chosen cut-offs and the bounds are 48038 and 99313. -/
theorem terminal_tangentHead :
    1073741824 * (67108863 + 2 * 16777216) < (357913943 - 8388608 - 16777216) ^ 2 ∧
    tangentHeadBound 1073741824 357913943 67108863 3 34 34 290805098 290805098
      16777216 8388608 = 48038 ∧
    tangentHeadBound 1073741824 357913943 67108863 4 34 34 302954072 302954072
      16777216 8388608 = 99313 := by
  decide

/-- Theorem D for a multiplicity-three interpolant at the last open error count
of the first-prime rate-1/4 bracket, value degrees two through six. -/
theorem firstPrime_quarter_tangentHead :
    1073741824 * (268435455 + 2 * 16777216) < (592794966 - 4194304 - 16777216) ^ 2 ∧
    tangentHeadBound 1073741824 592794966 268435455 2 23 23 1778384897 1778384897
      16777216 4194304 = 56175 ∧
    tangentHeadBound 1073741824 592794966 268435455 3 23 23 1778384897 1778384897
      16777216 4194304 = 176645 ∧
    tangentHeadBound 1073741824 592794966 268435455 4 23 23 1778384897 1778384897
      16777216 4194304 = 374183 ∧
    tangentHeadBound 1073741824 592794966 268435455 5 23 23 1778384897 1778384897
      16777216 4194304 = 648789 ∧
    tangentHeadBound 1073741824 592794966 268435455 6 23 23 1778384897 1778384897
      16777216 4194304 = 1000463 := by
  decide

#print axioms packing_of_second_moment
#print axioms terminal_tangentHead
#print axioms firstPrime_quarter_tangentHead
#print axioms sq_le_mul_of_nonpos
#print axioms bessel_of_hodge
#print axioms card_large_miss_le
#print axioms common_card_gt
#print axioms terminal_weightFree

end ProximityGap.HodgeSectionLattice
