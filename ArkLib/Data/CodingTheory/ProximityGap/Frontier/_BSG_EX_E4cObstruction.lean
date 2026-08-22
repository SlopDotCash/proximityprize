/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_DRC1

/-!
# BSG `E4c` — the difference-representation obstruction (REFUTED countermodel)

This file records, with a **machine-checked countermodel**, why the *naive elementary
representation route* for the difference bound in dependent random choice (the `E4` step of
`BareDRCExtract`) does **not** close. It is a refutation marker, not a proven theorem: it
redirects the `E4` step to the Ruzsa-triangle / Plünnecke route (`E4d`).

## The naive (false) claim

The hard half of `BareDRCExtract` is the *small-doubling* bound `#(A'' - A'') ≤ C · #A''`. The
proven counting bricks `E4a`/`E4b` show that if **every** difference `d ∈ A'' - A''` has at least
`t` representations as a pair `(x, y) ∈ A'' ×ˢ A''` with `x - y = d`, then
`#(A'' - A'') · t ≤ #A'' ^ 2`. So one is tempted to *supply* the representation lower bound from
the common-neighbour data:

> For `a, a' ∈ A''` and a common neighbour `w` (`(a, w), (a', w) ∈ G`, `w ∈ A`), the difference
> `d = a - a'` factors as `(a - w) - (a' - w)`. If the pair `(a, a')` has `t` common neighbours,
> these `t` factorisations would give `t` representations of `d`, so `r_{A'' - A''}(d) ≥ t`.

This is **FALSE**. The `t` pairs `(a - w, a' - w)` are *not* elements of `A'' ×ˢ A''` (in general
`a - w ∉ A''`). The factorisation lives in the *difference set*, not inside `A''`; it provides no
lower bound on `r_{A'' - A''}`. This is exactly the genuine dependent-random-choice subtlety: the
small-doubling control comes from the Ruzsa triangle inequality applied to the *common-neighbour
density*, not from a naive per-difference representation count.

## The countermodel

`NaiveDiffReps` below is the naive claim, stated cleanly. `naiveDiffReps_REFUTED` is a complete
machine-checked countermodel over `ℤ`:

* `A = {0, 1, 5, 6}`, `A'' = {0, 1}`, `G = {(0,5), (1,5), (0,6), (1,6)}`, threshold `t = 2`.
* **Every** pair `(a, a') ∈ A'' ×ˢ A''` has *exactly* `2 = t` common neighbours (both `0` and `1`
  are adjacent to both `5` and `6`), so the hypothesis of `NaiveDiffReps` holds.
* The difference `d = 1 ∈ A'' - A''` has only the **single** representation `(1, 0)` inside
  `A'' ×ˢ A''` (the only ordered pair from `{0,1}²` with `x - y = 1`), so
  `r_{A'' - A''}(1) = 1 < 2 = t`. The conclusion fails.

Hence the elementary route is dead; `E4` must go through `E4d` (Ruzsa triangle).

## References

* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6 (dependent random choice).
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), §2.5 (Ruzsa calculus).
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- The **number of representations** of a difference `d` as `x - y` with `(x, y) ∈ A'' ×ˢ A''`. -/
noncomputable def diffReps (A'' : Finset α) (d : α) : ℕ :=
  #{p ∈ A'' ×ˢ A'' | p.1 - p.2 = d}

/-- **The naive (false) difference-representation claim.** If every left-pair drawn from `A''` has
at least `t` common neighbours in `(A, G)`, then every difference in `A'' - A''` has at least `t`
representations *inside* `A'' ×ˢ A''`. (This is what one would need to feed `E4b`; it is false.) -/
def NaiveDiffReps : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A A'' : Finset α) (G : Finset (α × α)) (t : ℕ),
      A'' ⊆ A →
      (∀ p ∈ A'' ×ˢ A'', t ≤ commonNeighbors A G p.1 p.2) →
      ∀ d ∈ A'' - A'', t ≤ diffReps A'' d

/-! ## The concrete countermodel over `ℤ` -/

/-- The left/right vertex set of the countermodel. -/
def cmA : Finset ℤ := {0, 1, 5, 6}

/-- The refined subset of the countermodel. -/
def cmA'' : Finset ℤ := {0, 1}

/-- The bipartite graph of the countermodel: `{0,1}` each joined to both `{5,6}`. -/
def cmG : Finset (ℤ × ℤ) := {(0, 5), (1, 5), (0, 6), (1, 6)}

/-- `A'' ⊆ A` in the countermodel. -/
lemma cmA''_subset : cmA'' ⊆ cmA := by decide

/-- Every pair from `A'' ×ˢ A''` has exactly the threshold-many (`= 2`) common neighbours. -/
lemma cm_commonNeighbors_ge :
    ∀ p ∈ cmA'' ×ˢ cmA'', (2 : ℕ) ≤ commonNeighbors cmA cmG p.1 p.2 := by
  decide

/-- The difference `1` lies in `A'' - A''`. -/
lemma cm_one_mem_diff : (1 : ℤ) ∈ cmA'' - cmA'' := by decide

/-- But the difference `1` has only **one** representation inside `A'' ×ˢ A''`, strictly fewer than
the threshold `2`. -/
lemma cm_diffReps_one : diffReps cmA'' (1 : ℤ) = 1 := by decide

/-- **`NaiveDiffReps` is refuted.** The countermodel above satisfies the hypothesis (every pair has
`≥ 2` common neighbours) but violates the conclusion (the difference `1` has only `1 < 2`
representations inside `A'' ×ˢ A''`). The naive factorisation `a - a' = (a - w) - (a' - w)` does
*not* produce representations inside `A''`. -/
theorem naiveDiffReps_REFUTED : ¬ NaiveDiffReps := by
  intro h
  -- Instantiate the claim at the countermodel; `2 ≤ diffReps cmA'' 1 = 1` is absurd.
  have hbad : (2 : ℕ) ≤ diffReps cmA'' (1 : ℤ) :=
    h cmA cmA'' cmG 2 cmA''_subset cm_commonNeighbors_ge (1 : ℤ) cm_one_mem_diff
  rw [cm_diffReps_one] at hbad
  omega

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.naiveDiffReps_REFUTED
