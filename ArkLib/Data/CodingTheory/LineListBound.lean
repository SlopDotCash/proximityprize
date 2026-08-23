/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The line list bound: the affinely-dependent dimension-1 case, unconditional (#389)

The window-interior δ\* (the proximity-prize core) reduces to the interleaved-list **count** bound
beyond Johnson; `reedSolomon_genpos_list_bound` handles the affinely-*independent* families
unconditionally (Vandermonde MDS), leaving the affinely-*dependent* case — which is a hyperplane
*incidence* count over the (linear) code, i.e. higher-order MDS for the explicit points.

This file proves the **dimension-1** slice of that incidence count *unconditionally*, for any code:

`line_agreement_card_le` — on a line of codewords `t ↦ f₀ + t·g`, the number of points agreeing
with a received word `y` on `≥ a` positions is `≤ n/(a−b)` (`b` = constant-agreement positions).
Each moving position matches at exactly one parameter, so the bad parameters' fibers are disjoint
and total `≤ n`.

This is genuine beyond-Johnson list control with **no genericity / higher-order-MDS hypothesis** —
it pins the affinely-dependent core in the `affine-dim = 1` regime.  The open part is the
higher-dimensional incidence (`affine-dim ≥ 2`), which is the GM-MDS question for explicit points.
Axiom-clean.
-/

open Finset

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]

/-- **The line list bound (unconditional beyond-Johnson, affinely-dependent dimension 1).**
On a line of codewords `t ↦ f₀ + t·g` in `F^ι`, the number of points agreeing with `y` on at
least `a` positions is `≤ n/(a−b)`, where `b` counts the constant-agreement positions
(`g i = 0 ∧ f₀ i = y i`).  Each moving position (`g i ≠ 0`) matches at exactly one parameter,
so the bad parameters' fibers are disjoint and total at most `n`.  Holds for *any* code. -/
theorem line_agreement_card_le (f₀ g y : ι → F) {a b : ℕ}
    (hb : (univ.filter (fun i => g i = 0 ∧ f₀ i = y i)).card = b) (hab : b < a) :
    (univ.filter (fun t : F => a ≤ (univ.filter (fun i => f₀ i + t * g i = y i)).card)).card
      * (a - b) ≤ Fintype.card ι := by
  classical
  -- agreement at `t` splits into the (constant) `b` and the moving fiber.
  have hagree : ∀ t : F,
      (univ.filter (fun i => f₀ i + t * g i = y i)).card
        = b + (univ.filter (fun i => g i ≠ 0 ∧ f₀ i + t * g i = y i)).card := by
    intro t
    rw [← hb, ← Finset.card_union_of_disjoint, Finset.filter_union_right]
    · refine congrArg Finset.card (Finset.filter_congr ?_)
      intro i _
      by_cases hg : g i = 0 <;> simp [hg]
    · rw [Finset.disjoint_left]
      rintro i hi hj
      exact (mem_filter.mp hj).2.1 (mem_filter.mp hi).2.1
  set B : Finset F :=
    univ.filter (fun t : F => a ≤ (univ.filter (fun i => f₀ i + t * g i = y i)).card) with hBdef
  have hBmove : ∀ t ∈ B, a - b ≤ (univ.filter (fun i => g i ≠ 0 ∧ f₀ i + t * g i = y i)).card := by
    intro t ht
    have := (mem_filter.mp ht).2
    rw [hagree t] at this; omega
  -- the moving fibers over distinct parameters are disjoint
  have hdisj : (B : Set F).PairwiseDisjoint
      (fun t => univ.filter (fun i => g i ≠ 0 ∧ f₀ i + t * g i = y i)) := by
    intro s _ t _ hst
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hj
    apply hst
    have hg : g i ≠ 0 := (mem_filter.mp hi).2.1
    have : s * g i = t * g i := by
      have h1 := (mem_filter.mp hi).2.2
      have h2 := (mem_filter.mp hj).2.2
      linear_combination h1 - h2
    exact mul_right_cancel₀ hg this
  have hsum : ∑ t ∈ B, (univ.filter (fun i => g i ≠ 0 ∧ f₀ i + t * g i = y i)).card
      ≤ Fintype.card ι := by
    rw [← Finset.card_biUnion hdisj]
    exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq (Finset.card_univ))
  calc B.card * (a - b) = ∑ _t ∈ B, (a - b) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ t ∈ B, (univ.filter (fun i => g i ≠ 0 ∧ f₀ i + t * g i = y i)).card :=
        Finset.sum_le_sum hBmove
    _ ≤ Fintype.card ι := hsum
