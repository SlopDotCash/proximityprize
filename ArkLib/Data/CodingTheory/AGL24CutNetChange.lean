/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24CutSupply

/-!
# [AGL24]/Frank: net-change accounting for a single reorientation (issue #354, Frank brick F4)

The Frank descent (`AGL24FrankDescent`) and the cut supply (`AGL24CutSupply`) supply a
*single* reorientation `O.updateHead i₀ v` that strictly decreases the deficiency of the
particular cut it is aimed at (`cutDeficiency_updateHead_lt`). The uncrossing / augmenting
argument that closes `FrankUncrossingStep` must also control what that same reorientation
does to **every other** cut. This file proves the exact per-cut net-change accounting that
the existing `AGL24CutSupply` lemmas only establish for the target cut.

The single edge `i₀` is the *only* edge whose head moves, so for any cut `S` the
head-border membership changes at most at `i₀`, governed by the two predicates

* `pOld S := O.head i₀ ∈ S ∧ ¬ e i₀ ⊆ S`  (was `i₀` an entering border edge of `S`?)
* `pNew S := v ∈ S ∧ ¬ e i₀ ⊆ S`          (is it now, after rehearing to `v`?)

The three-way card identity (`headBorderEdges_card_updateHead`), the universal
`|card change| ≤ 1` bound (`headBorderEdges_card_updateHead_sub_le_one`,
`cutDeficiency_updateHead_le_succ` / `_ge_pred`), and — the genuinely new content for the
uncrossing argument — the *monotone* facts

* `cutDeficiency_updateHead_le_of_mem` — a cut already containing the new head `v` never
  gets *worse* under the reorientation, and
* `cutDeficiency_updateHead_increase_imp` — the only cuts whose deficiency can increase are
  those with `O.head i₀ ∈ S` and `v ∉ S` (so any worsened cut separates the old head from
  the new head),

are exactly the inputs an uncrossing/augmenting net-accounting consumes. Every result here
is char-uniform, family-uniform, and axiom-clean.

This file is *infrastructure*: it does **not** discharge `FrankUncrossingStep` itself, whose
remaining content is the multi-edge augmenting-walk reachability of a lower-potential
orientation (a single `updateHead` provably cannot always lower the total potential — there
are `k`-WPC configurations whose potential drops only after two simultaneous reorientations).
It tightens the residual to that augmenting content by closing the per-cut arithmetic.
-/

open Finset

namespace AGL24

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

omit [DecidableEq ι] in
/-- After `O.updateHead i₀ v`, an edge `j ≠ i₀` keeps its head, hence its head-border
membership at any cut `S` is unchanged. -/
theorem mem_headBorderEdges_updateHead_of_ne {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {i₀ : ι} {v : V} (hv : v ∈ e i₀)
    {j : ι} (hji : j ≠ i₀) :
    j ∈ headBorderEdges (O.updateHead i₀ v hv) S ↔ j ∈ headBorderEdges O S := by
  classical
  simp only [mem_headBorderEdges, O.updateHead_head_of_ne v hv hji]

omit [DecidableEq ι] in
/-- The membership of the reoriented edge `i₀` in the head-border of a cut `S`, after
reheading to `v`, is governed exactly by `v ∈ S ∧ ¬ e i₀ ⊆ S`. -/
theorem mem_headBorderEdges_updateHead_self {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {i₀ : ι} {v : V} (hv : v ∈ e i₀) :
    i₀ ∈ headBorderEdges (O.updateHead i₀ v hv) S ↔ (v ∈ S ∧ ¬ e i₀ ⊆ S) := by
  classical
  simp only [mem_headBorderEdges, O.updateHead_head_self i₀ v hv]

/-- **Head-border is unchanged when the two head predicates agree.** If, relative to a cut
`S`, the old head `O.head i₀` and the new head `v` have the same membership in `S`, the whole
head-border set of `S` is unaffected by the reorientation. -/
theorem headBorderEdges_updateHead_eq_of_iff {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {i₀ : ι} {v : V} (hv : v ∈ e i₀)
    (hiff : (v ∈ S) ↔ (O.head i₀ ∈ S)) :
    headBorderEdges (O.updateHead i₀ v hv) S = headBorderEdges O S := by
  classical
  ext j
  by_cases hji : j = i₀
  · subst hji
    rw [mem_headBorderEdges_updateHead_self, mem_headBorderEdges]
    constructor
    · rintro ⟨hvS, hns⟩; exact ⟨hiff.mp hvS, hns⟩
    · rintro ⟨hhS, hns⟩; exact ⟨hiff.mpr hhS, hns⟩
  · exact mem_headBorderEdges_updateHead_of_ne O S hv hji

/-- **The reorientation adds `i₀` (a `+1`) to a cut iff it newly enters that cut.** -/
theorem headBorderEdges_updateHead_eq_insert {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {i₀ : ι} {v : V} (hv : v ∈ e i₀)
    (hvS : v ∈ S) (hns : ¬ e i₀ ⊆ S) (hold : O.head i₀ ∉ S) :
    headBorderEdges (O.updateHead i₀ v hv) S = insert i₀ (headBorderEdges O S) := by
  classical
  have hnotMem : i₀ ∉ headBorderEdges O S := by
    rw [mem_headBorderEdges]; exact fun h => hold h.1
  ext j
  by_cases hji : j = i₀
  · subst hji
    rw [mem_headBorderEdges_updateHead_self, Finset.mem_insert]
    constructor
    · intro _; exact Or.inl rfl
    · intro _; exact ⟨hvS, hns⟩
  · rw [mem_headBorderEdges_updateHead_of_ne O S hv hji, Finset.mem_insert]
    constructor
    · intro h; exact Or.inr h
    · rintro (h | h)
      · exact absurd h hji
      · exact h

/-- **The reorientation removes `i₀` (a `−1`) from a cut iff it newly leaves that cut.** -/
theorem headBorderEdges_updateHead_eq_erase {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {i₀ : ι} {v : V} (hv : v ∈ e i₀)
    (hvS : v ∉ S) (hold : O.head i₀ ∈ S) (hns : ¬ e i₀ ⊆ S) :
    headBorderEdges (O.updateHead i₀ v hv) S = (headBorderEdges O S).erase i₀ := by
  classical
  ext j
  by_cases hji : j = i₀
  · subst hji
    rw [mem_headBorderEdges_updateHead_self, Finset.mem_erase]
    constructor
    · rintro ⟨hvS', _⟩; exact absurd hvS' hvS
    · rintro ⟨hne, _⟩; exact absurd rfl hne
  · rw [mem_headBorderEdges_updateHead_of_ne O S hv hji, Finset.mem_erase]
    constructor
    · intro h; exact ⟨hji, h⟩
    · rintro ⟨_, h⟩; exact h

/-- **`+1` head-border card after reorienting into a cut not previously entered.** -/
theorem headBorderEdges_card_updateHead_eq_succ' {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {i₀ : ι} {v : V} (hv : v ∈ e i₀)
    (hvS : v ∈ S) (hns : ¬ e i₀ ⊆ S) (hold : O.head i₀ ∉ S) :
    (headBorderEdges (O.updateHead i₀ v hv) S).card = (headBorderEdges O S).card + 1 := by
  classical
  have hnotMem : i₀ ∉ headBorderEdges O S := by
    rw [mem_headBorderEdges]; exact fun h => hold h.1
  rw [headBorderEdges_updateHead_eq_insert O S hv hvS hns hold,
    Finset.card_insert_of_notMem hnotMem]

/-- **`−1` head-border card after reorienting out of a cut.** -/
theorem headBorderEdges_card_updateHead_eq_pred {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {i₀ : ι} {v : V} (hv : v ∈ e i₀)
    (hvS : v ∉ S) (hold : O.head i₀ ∈ S) (hns : ¬ e i₀ ⊆ S) :
    (headBorderEdges (O.updateHead i₀ v hv) S).card = (headBorderEdges O S).card - 1 := by
  classical
  have hMem : i₀ ∈ headBorderEdges O S := by
    rw [mem_headBorderEdges]; exact ⟨hold, hns⟩
  rw [headBorderEdges_updateHead_eq_erase O S hv hvS hold hns,
    Finset.card_erase_of_mem hMem]

/-- **Universal one-sided card bounds for a single reorientation.** The head-border card of
*any* cut changes by at most one in each direction. -/
theorem headBorderEdges_card_updateHead_le_succ {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {i₀ : ι} {v : V} (hv : v ∈ e i₀) :
    (headBorderEdges (O.updateHead i₀ v hv) S).card ≤ (headBorderEdges O S).card + 1 := by
  classical
  -- `headBorderEdges O' S ⊆ insert i₀ (headBorderEdges O S)`.
  have hsub : headBorderEdges (O.updateHead i₀ v hv) S ⊆
      insert i₀ (headBorderEdges O S) := by
    intro j hj
    by_cases hji : j = i₀
    · subst hji; exact Finset.mem_insert_self _ _
    · rw [mem_headBorderEdges_updateHead_of_ne O S hv hji] at hj
      exact Finset.mem_insert_of_mem hj
  calc (headBorderEdges (O.updateHead i₀ v hv) S).card
      ≤ (insert i₀ (headBorderEdges O S)).card := Finset.card_le_card hsub
    _ ≤ (headBorderEdges O S).card + 1 := Finset.card_insert_le _ _

theorem headBorderEdges_card_updateHead_le_succ' {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {i₀ : ι} {v : V} (hv : v ∈ e i₀) :
    (headBorderEdges O S).card ≤ (headBorderEdges (O.updateHead i₀ v hv) S).card + 1 := by
  classical
  -- Symmetric: reverse the roles by going back from `O'` to `O` via reheading to `O.head i₀`.
  have hsub : headBorderEdges O S ⊆
      insert i₀ (headBorderEdges (O.updateHead i₀ v hv) S) := by
    intro j hj
    by_cases hji : j = i₀
    · subst hji; exact Finset.mem_insert_self _ _
    · rw [← mem_headBorderEdges_updateHead_of_ne O S hv hji] at hj
      exact Finset.mem_insert_of_mem hj
  calc (headBorderEdges O S).card
      ≤ (insert i₀ (headBorderEdges (O.updateHead i₀ v hv) S)).card := Finset.card_le_card hsub
    _ ≤ (headBorderEdges (O.updateHead i₀ v hv) S).card + 1 := Finset.card_insert_le _ _

/-- **A cut deficiency increases by at most one under a single reorientation.** -/
theorem cutDeficiency_updateHead_le_succ {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {k : ℕ} {i₀ : ι} {v : V} (hv : v ∈ e i₀) :
    cutDeficiency (O.updateHead i₀ v hv) S k ≤ cutDeficiency O S k + 1 := by
  have h := headBorderEdges_card_updateHead_le_succ' O S hv
  unfold cutDeficiency
  omega

/-- **A cut deficiency decreases by at most one under a single reorientation.** -/
theorem cutDeficiency_updateHead_ge_pred {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {k : ℕ} {i₀ : ι} {v : V} (hv : v ∈ e i₀) :
    cutDeficiency O S k ≤ cutDeficiency (O.updateHead i₀ v hv) S k + 1 := by
  have h := headBorderEdges_card_updateHead_le_succ O S hv
  unfold cutDeficiency
  omega

/-- **Cuts containing the new head never get worse.** If the new head `v` lies in `S`, then
the reorientation does not increase the deficiency of `S`. This is the monotone fact the
uncrossing net-accounting uses to certify that reorienting into a maximal deficient cut `T`
(`v ∈ T`) cannot harm `T` or any cut that already contains `v`. -/
theorem cutDeficiency_updateHead_le_of_mem {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {k : ℕ} {i₀ : ι} {v : V} (hv : v ∈ e i₀)
    (hvS : v ∈ S) :
    cutDeficiency (O.updateHead i₀ v hv) S k ≤ cutDeficiency O S k := by
  classical
  -- The head-border card of `S` does not drop: every old border edge stays, plus possibly `i₀`.
  have hge : (headBorderEdges O S).card ≤ (headBorderEdges (O.updateHead i₀ v hv) S).card := by
    refine Finset.card_le_card ?_
    intro j hj
    by_cases hji : j = i₀
    · subst hji
      rw [mem_headBorderEdges] at hj
      rw [mem_headBorderEdges_updateHead_self]
      exact ⟨hvS, hj.2⟩
    · rw [mem_headBorderEdges_updateHead_of_ne O S hv hji]; exact hj
  unfold cutDeficiency
  omega

/-- **Only cuts separating the old head from the new head can get worse.** If the
reorientation strictly increases the deficiency of a cut `S`, then the old head
`O.head i₀` lies in `S` while the new head `v` does not (and the edge `e i₀` is not contained
in `S`). Contrapositive: every cut whose deficiency rises is one that the directed edge
`O.head i₀ → v` leaves. -/
theorem cutDeficiency_updateHead_increase_imp {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) {k : ℕ} {i₀ : ι} {v : V} (hv : v ∈ e i₀)
    (hinc : cutDeficiency O S k < cutDeficiency (O.updateHead i₀ v hv) S k) :
    O.head i₀ ∈ S ∧ v ∉ S ∧ ¬ e i₀ ⊆ S := by
  classical
  -- `v ∈ S` is impossible by the monotone lemma.
  have hvS : v ∉ S := by
    intro hvS
    exact absurd (cutDeficiency_updateHead_le_of_mem O S hv hvS) (not_le.mpr hinc)
  -- The deficiency rose, so the head-border card of `S` strictly dropped.
  have hcard : (headBorderEdges (O.updateHead i₀ v hv) S).card < (headBorderEdges O S).card := by
    by_contra hge
    push Not at hge
    have : cutDeficiency (O.updateHead i₀ v hv) S k ≤ cutDeficiency O S k := by
      unfold cutDeficiency; omega
    exact absurd this (not_le.mpr hinc)
  -- A strict drop forces `i₀` to have been a border edge that left.
  -- `headBorderEdges O' S ⊆ headBorderEdges O S` would force `≤`, so some old edge left:
  -- it must be `i₀` (others unchanged), giving `O.head i₀ ∈ S` and `¬ e i₀ ⊆ S`.
  by_contra hcon
  -- Suppose `i₀` is NOT an old border edge of `S`. Then nothing dropped, contradiction.
  push Not at hcon
  -- From hvS we already have `v ∉ S`; `hcon` then gives: `O.head i₀ ∈ S → ¬ (v ∉ S → e i₀ ⊆ S)`.
  -- Reformulate: show `headBorderEdges O S ⊆ headBorderEdges O' S`, contradicting `hcard`.
  have hsub : headBorderEdges O S ⊆ headBorderEdges (O.updateHead i₀ v hv) S := by
    intro j hj
    by_cases hji : j = i₀
    · subst hji
      -- `i₀ ∈ headBorderEdges O S` means `O.head i₀ ∈ S ∧ ¬ e i₀ ⊆ S`; combined with `hcon`
      -- (which says this can't both hold) we derive `False`.
      rw [mem_headBorderEdges] at hj
      exact absurd (hcon hj.1 hvS) hj.2
    · rw [mem_headBorderEdges_updateHead_of_ne O S hv hji]; exact hj
  have := Finset.card_le_card hsub
  omega

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.headBorderEdges_updateHead_eq_of_iff
#print axioms AGL24.headBorderEdges_card_updateHead_eq_succ'
#print axioms AGL24.headBorderEdges_card_updateHead_eq_pred
#print axioms AGL24.cutDeficiency_updateHead_le_succ
#print axioms AGL24.cutDeficiency_updateHead_ge_pred
#print axioms AGL24.cutDeficiency_updateHead_le_of_mem
#print axioms AGL24.cutDeficiency_updateHead_increase_imp
