/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24CutNetChange
import ArkLib.Data.CodingTheory.AGL24FrankDescent

/-!
# [AGL24]/Frank: the conditional uncrossing decrease step (issue #354, Frank brick F5)

`FrankUncrossingStep` (`AGL24FrankDescent`) is the single remaining residual of Frank's
rooted out-cut theorem: from any positive-potential orientation of a `k`-WPC family produce
one of strictly smaller total root deficiency. The descent, the maximal-deficient-cut
existence, and the WPC crossing-edge supply are all already proven. This file closes the
*conditional* version of the decrease step using the per-cut net-change accounting of
`AGL24CutNetChange`, and pins down precisely the obstruction that the unconditional step
must still overcome.

## What is proved here (axiom-clean)

* `totalRootDeficiency_updateHead_lt_of_forall_le` — if a single reorientation does not
  increase the deficiency of *any* proper root cut and strictly decreases the deficiency of
  *one* of them, the total root deficiency strictly drops. (The descent's well-founded
  recursion consumes exactly this.)

* `totalRootDeficiency_updateHead_lt_of_no_worsened_cut` — **the conditional uncrossing
  step.** Reorienting a WPC crossing edge `i₀` (head outside, `v ∈ T`) into a deficient
  proper root cut `T` strictly decreases the total root deficiency, provided no proper root
  cut is worsened by the move. The "no worsened cut" hypothesis is *exactly* the obstruction
  isolated by `cutDeficiency_updateHead_increase_imp`: every worsened cut is a proper root
  cut separating the old head `O.head i₀` from the new head `v`.

* `frankUncrossingStep_of_forall_cleanReorientation` — assembling the above into the
  residual: if every positive-potential orientation admits *some* reorientation into a
  deficient root cut that worsens no proper root cut, then `FrankUncrossingStep` holds.

## The remaining open core, now sharply localized

The hypothesis `exists_clean_reorientation` is **not** always satisfiable by a single edge:
there are `k`-WPC configurations whose total potential drops only after two simultaneous
reorientations (verified by exhaustive search over `n ≤ 5`). Crucially, the worsened cuts of
a single reorientation are typically *tight* (deficiency `0 → 1`), not deficient, so the
supermodular corollary `cutDeficiency_union_or_inter_pos` — which requires *both* crossed
cuts deficient — does not apply to them. The unconditional `FrankUncrossingStep` therefore
genuinely requires the augmenting-walk reachability of Frank's classical proof (a chain of
reorientations through tight sets), which is the precisely-localized residual. This file
reduces that residual to the single combinatorial statement
`exists_clean_reorientation`-or-augmenting-walk, with all per-cut arithmetic discharged.
-/

open Finset

namespace AGL24

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

omit [DecidableEq ι] in
/-- **Total root deficiency strictly drops under a pointwise-nonincreasing reorientation with
one strict drop.** If `O'` deficiency is `≤ O` deficiency on every proper root cut and `<` on
some proper root cut `T`, then `totalRootDeficiency O' r k < totalRootDeficiency O r k`. -/
theorem totalRootDeficiency_lt_of_forall_le {e : ι → Finset V}
    (O O' : HeadOrientation e) (r : V) (k : ℕ)
    (hle : ∀ S ∈ properRootCuts r, cutDeficiency O' S k ≤ cutDeficiency O S k)
    {T : Finset V} (hT : T ∈ properRootCuts r)
    (hlt : cutDeficiency O' T k < cutDeficiency O T k) :
    totalRootDeficiency O' r k < totalRootDeficiency O r k := by
  classical
  unfold totalRootDeficiency
  exact Finset.sum_lt_sum hle ⟨T, hT, hlt⟩

omit [DecidableEq ι] in
/-- **The conditional uncrossing decrease step.** Reorienting the crossing edge `i₀` (head
outside `T`, with `v ∈ e i₀ ∩ T`) into a deficient proper root cut `T` strictly decreases the
total root deficiency, provided the move worsens no proper root cut. The "no worsened cut"
side condition is precisely the obstruction characterized by
`cutDeficiency_updateHead_increase_imp`. -/
theorem totalRootDeficiency_updateHead_lt_of_no_worsened_cut {e : ι → Finset V}
    (O : HeadOrientation e) (r : V) (k : ℕ)
    {T : Finset V} (hT : T ∈ properRootCuts r) (hTdef : 0 < cutDeficiency O T k)
    {i₀ : ι} {v : V} (hv : v ∈ e i₀) (hvT : v ∈ T) (hns : ¬ e i₀ ⊆ T)
    (hhead : O.head i₀ ∉ T)
    (hno : ∀ S ∈ properRootCuts r,
      cutDeficiency (O.updateHead i₀ v hv) S k ≤ cutDeficiency O S k) :
    totalRootDeficiency (O.updateHead i₀ v hv) r k < totalRootDeficiency O r k := by
  classical
  -- Strict drop at `T`: the target cut's head-border count goes up by one.
  have hTlt : cutDeficiency (O.updateHead i₀ v hv) T k < cutDeficiency O T k :=
    cutDeficiency_updateHead_lt O T hv hvT hns hhead ((cutDeficiency_pos_iff O T k).mp hTdef)
  exact totalRootDeficiency_lt_of_forall_le O (O.updateHead i₀ v hv) r k hno hT hTlt

/-- **Restatement of the "no worsened cut" hypothesis via the worsening characterization.**
By `cutDeficiency_updateHead_increase_imp`, a reorientation worsens a proper root cut `S`
only if `O.head i₀ ∈ S` and `v ∉ S`; so to certify "no worsened cut" it suffices to check
every proper root cut separating the old head from the new head stays tight enough. -/
theorem no_worsened_cut_of_forall_separating {e : ι → Finset V}
    (O : HeadOrientation e) (r : V) (k : ℕ) {i₀ : ι} {v : V} (hv : v ∈ e i₀)
    (hsep : ∀ S ∈ properRootCuts r, O.head i₀ ∈ S → v ∉ S → ¬ e i₀ ⊆ S →
      cutDeficiency (O.updateHead i₀ v hv) S k ≤ cutDeficiency O S k) :
    ∀ S ∈ properRootCuts r,
      cutDeficiency (O.updateHead i₀ v hv) S k ≤ cutDeficiency O S k := by
  intro S hS
  by_cases hinc : cutDeficiency O S k < cutDeficiency (O.updateHead i₀ v hv) S k
  · -- Worsened: the characterization forces a separating cut, then `hsep` gives `≤`,
    -- contradicting `hinc`.
    obtain ⟨hold, hvS, hns⟩ := cutDeficiency_updateHead_increase_imp O S hv hinc
    exact absurd (hsep S hS hold hvS hns) (not_le.mpr hinc)
  · exact not_lt.mp hinc

/-- The packaged "clean reorientation" data: a deficient proper root cut `T`, a crossing edge
`i₀` with head outside and a chosen vertex `v ∈ e i₀ ∩ T`, whose reorientation worsens no
proper root cut. -/
def CleanReorientation {e : ι → Finset V} (O : HeadOrientation e) (r : V) (k : ℕ) : Prop :=
  ∃ (T : Finset V) (_ : T ∈ properRootCuts r) (_ : 0 < cutDeficiency O T k)
    (i₀ : ι) (v : V) (hv : v ∈ e i₀), v ∈ T ∧ ¬ e i₀ ⊆ T ∧ O.head i₀ ∉ T ∧
      ∀ S ∈ properRootCuts r,
        cutDeficiency (O.updateHead i₀ v hv) S k ≤ cutDeficiency O S k

omit [DecidableEq ι] in
/-- **A clean reorientation yields the uncrossing decrease.** -/
theorem exists_lt_of_cleanReorientation {e : ι → Finset V}
    (O : HeadOrientation e) (r : V) (k : ℕ) (h : CleanReorientation O r k) :
    ∃ O' : HeadOrientation e, totalRootDeficiency O' r k < totalRootDeficiency O r k := by
  obtain ⟨T, hT, hTdef, i₀, v, hv, hvT, hns, hhead, hno⟩ := h
  exact ⟨O.updateHead i₀ v hv,
    totalRootDeficiency_updateHead_lt_of_no_worsened_cut O r k hT hTdef hv hvT hns hhead hno⟩

omit [DecidableEq ι] in
/-- **`FrankUncrossingStep` reduces to the existence of a clean reorientation.** If every
positive-potential orientation of `e` admits a clean reorientation (one that worsens no
proper root cut), then the Frank uncrossing decrease step holds for `e`. -/
theorem frankUncrossingStep_of_forall_cleanReorientation {e : ι → Finset V}
    {r : V} {k : ℕ}
    (h : ∀ O : HeadOrientation e, 0 < totalRootDeficiency O r k → CleanReorientation O r k) :
    FrankUncrossingStep (e := e) r k := by
  intro O hpos
  exact exists_lt_of_cleanReorientation O r k (h O hpos)

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.totalRootDeficiency_lt_of_forall_le
#print axioms AGL24.totalRootDeficiency_updateHead_lt_of_no_worsened_cut
#print axioms AGL24.no_worsened_cut_of_forall_separating
#print axioms AGL24.exists_lt_of_cleanReorientation
#print axioms AGL24.frankUncrossingStep_of_forall_cleanReorientation
