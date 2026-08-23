/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs

/-!
# Reducing the MCA bad-scalar count to the line's list size (#232)

The Mutual Correlated Agreement error is `ε_mca = (#bad γ)/q`, where `γ` is **bad** when the line
`u₀ + γ·u₁` agrees with some codeword on `≥ t = (1-δ)·n` of the `n` evaluation points. The prize asks
to bound `#bad γ` by a constant (independent of `q`). This file proves the **pigeonhole reduction**
that cuts the problem down to the line's list size:

* `pigeonhole_large_fibers` — for any `h : ι → κ`, at most `n/t` values are hit by `h` at least `t`
  times (`t · #{y : |h⁻¹(y)| ≥ t} ≤ n`, where `n = |ι|`).

**Application (the reduction).** Fix the agreement codeword `P`. Where `u₁(x) ≠ 0`, a coordinate `x`
is matched by the *single* scalar `γ_x(P) = (P(x) - u₀(x))/u₁(x)`. A scalar `γ` with `≥ t` agreement
against `P` therefore has `≥ t` coordinates `x` with `γ_x(P) = γ`. Applying the pigeonhole to
`x ↦ γ_x(P)` gives **at most `n/t` bad scalars per codeword `P`**. Hence

`#bad γ ≤ (#distinct agreement codewords) · n/t = (line list size) · 1/(1-δ)`.

So `ε_mca` is bounded by a *constant* (in `q`) **iff** the line `{u₀ + γu₁ : γ}` has a list size
bounded in `q` at radius `δ`. The prize is thereby reduced to a list-decoding bound for the line —
which is known (poly) below the Johnson radius and is exactly the open question past it. This file
proves the reduction's combinatorial core, axiom-clean; it does not resolve the open list bound.
-/

namespace ArkLib.CodingTheory.MCAReduction

open Finset

/-- **Pigeonhole on large fibers.** For a map `h : ι → κ` on a finite type `ι` (`|ι| = n`), the number
of target values hit at least `t` times is at most `n/t`; equivalently `t · #{y : |h⁻¹(y)| ≥ t} ≤ n`.
The large fibers are disjoint and each has size `≥ t`, so `t` times their count is at most `n`. -/
theorem pigeonhole_large_fibers {ι : Type*} [Fintype ι] {κ : Type*} [DecidableEq κ]
    (h : ι → κ) (t : ℕ) :
    t * ((Finset.univ.image h).filter
        (fun y => t ≤ (Finset.univ.filter (fun i => h i = y)).card)).card
      ≤ Fintype.card ι := by
  classical
  set B : Finset κ := (Finset.univ.image h).filter
    (fun y => t ≤ (Finset.univ.filter (fun i => h i = y)).card) with hB
  -- the fibers over all image values partition `ι`
  have hpart : Fintype.card ι
      = ∑ y ∈ Finset.univ.image h, (Finset.univ.filter (fun i => h i = y)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise
      (fun i _ => Finset.mem_image_of_mem h (Finset.mem_univ i))
  -- each value in `B` has a fiber of size `≥ t`
  have h1 : (∑ _y ∈ B, t) ≤ ∑ y ∈ B, (Finset.univ.filter (fun i => h i = y)).card := by
    refine Finset.sum_le_sum (fun y hy => ?_)
    rw [hB, Finset.mem_filter] at hy
    exact hy.2
  -- `B`'s fiber sum is at most the full partition sum
  have h2 : (∑ y ∈ B, (Finset.univ.filter (fun i => h i = y)).card) ≤ Fintype.card ι := by
    rw [hpart]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  simp only [Finset.sum_const, smul_eq_mul] at h1
  rw [Nat.mul_comm]
  omega

#print axioms pigeonhole_large_fibers

end ArkLib.CodingTheory.MCAReduction
