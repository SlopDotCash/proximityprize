/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# Univariate polynomial agreement soundness (FRI / sum-check round)

Two distinct univariate polynomials of degree `≤ d` over a field `F` agree at at most `d` points
(their difference is a nonzero degree-`≤ d` polynomial, with at most `degree` roots).  In
probability form, a uniformly random point witnesses agreement with probability `≤ d/|F|`.

This is the soundness of one FRI folding / univariate sum-check round (the prover commits to a
claimed low-degree polynomial; a random evaluation catches any deviation except with probability
`d/|F|`) — the classical Schwartz–Zippel / DeMillo–Lipton bound in one variable.
-/

namespace Polynomial

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Univariate agreement count bound.**  Two distinct polynomials of degree `≤ d` agree at at
most `d` points. -/
theorem card_agree_le_of_ne {p q : F[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (hpq : p ≠ q) :
    (Finset.univ.filter (fun x : F => p.eval x = q.eval x)).card ≤ d := by
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  -- every agreement point is a root of `p - q`
  have hsub : (Finset.univ.filter (fun x : F => p.eval x = q.eval x))
      ⊆ (p - q).roots.toFinset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Multiset.mem_toFinset, mem_roots hne]
    simp only [IsRoot.def, eval_sub, sub_eq_zero]
    exact hx.2
  calc (Finset.univ.filter (fun x : F => p.eval x = q.eval x)).card
      ≤ (p - q).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (p - q).roots := Multiset.toFinset_card_le _
    _ ≤ (p - q).natDegree := card_roots' _
    _ ≤ max p.natDegree q.natDegree := natDegree_sub_le p q
    _ ≤ d := max_le hp hq

/-- **Univariate agreement probability bound.**  Two distinct degree-`≤ d` polynomials agree at a
uniformly random point with probability at most `d/|F|`: `|agree| · |F| ≤ d · |F|^?` — here in the
clean `|agree| / |F| ≤ d / |F|` ratio form (the FRI / univariate sum-check round soundness). -/
theorem prob_agree_le_of_ne {p q : F[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (hpq : p ≠ q) :
    let N : ℕ := (Finset.univ.filter (fun x : F => p.eval x = q.eval x)).card
    (N : ℝ) / (Fintype.card F : ℝ) ≤ (d : ℝ) / (Fintype.card F : ℝ) := by
  intro N
  have hcard : (N : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr (card_agree_le_of_ne hp hq hpq)
  exact div_le_div_of_nonneg_right hcard (by positivity)

end Polynomial
