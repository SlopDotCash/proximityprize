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
`u₀ + γ·u₁` agrees with some codeword on a set of `≥ t = (1-δ)·n` of the `n` evaluation points on
which the pair `(u₀, u₁)` is not jointly agreeing. The prize asks to bound `#bad γ` by a constant
(independent of `q`). This file proves only the **combinatorial pigeonhole ingredient** of a
per-codeword reduction:

* `pigeonhole_large_fibers` — for any `h : ι → κ`, at most `n/t` values are hit by `h` at least `t`
  times (`t · #{y : |h⁻¹(y)| ≥ t} ≤ n`, where `n = |ι|`).

**Intended application, with its hypotheses (audit PG-043; not formalized here).** Fix the
agreement codeword `P`. Let `Z = {x : u₁(x) = 0}`. Where `u₁(x) ≠ 0`, a coordinate `x` is matched
by the *single* scalar `γ_x(P) = (P(x) - u₀(x))/u₁(x)`. On `Z`, however, agreement with `P` does
not depend on `γ` at all: `x ∈ Z` agrees for *every* `γ` iff `u₀(x) = P(x)`. Writing
`z_P = #{x ∈ Z : u₀(x) = P(x)}`, a scalar `γ` with `≥ t` agreement against `P` has only
`≥ t - z_P` coordinates `x ∉ Z` with `γ_x(P) = γ`. Applying the pigeonhole to `x ↦ γ_x(P)` on the
`n - |Z|` coordinates outside `Z` therefore gives

* at most `(n - |Z|)/(t - z_P)` scalars with `≥ t` agreement against `P`, **when `t > z_P`**;
* at most `n/t` such scalars **when `u₁` is nowhere zero** (`Z = ∅`);
* no bound at all from this argument when `z_P ≥ t` (then every `γ` agrees with `P` on `≥ t`
  points).

The plain `n/t` per-codeword bound is false without such a hypothesis, even for genuine local MCA
witnesses: over `F₅`, length-`4` constant code, `t = 3`, `u₁ = (0,0,1,1)`, `u₀ = (0,0,-1,-2)`,
`P = 0`. The scalars `1` and `2` each agree with `P` on three coordinates (the first two plus the
third, resp. fourth); each witness contains a zero and a nonzero entry of `u₁`, so `u₁` agrees with
no constant there and both are MCA events. Two bad scalars share `P`, while `⌊n/t⌋ = 1`.

Under the nowhere-zero hypothesis one gets
`#bad γ ≤ (#distinct agreement codewords) · n/t = (line list size) · 1/(1-δ)`, so a `q`-independent
line list size *implies* a `q`-independent `#bad γ`. The **converse** (a bounded bad-scalar count
forcing a bounded line list size) is *not* proved here or supplied by this argument. This file
proves only the pigeonhole core, axiom-clean; it neither formalizes the per-codeword reduction nor
resolves the open list bound.
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
