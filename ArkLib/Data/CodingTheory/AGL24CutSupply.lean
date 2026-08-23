/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24WeakPartition
import ArkLib.Data.CodingTheory.AGL24Orientation

/-!
# [AGL24]/Frank: the cut supply — every cut of a WPC hypergraph has `k` border edges
# (issue #354, Frank front, brick F1)

The first brick of the `FrankOrientationResidual` campaign: weak partition connectivity
applied to a **two-cell partition** `{T, Tᶜ}` yields the cut condition that Frank's
orientation theorem consumes — every proper nonempty vertex subset is crossed by at least
`k` edges. (This is the *necessary* side of the orientation theorem and the supply that any
greedy/uncrossing construction of the crossing-orientation must draw on; it also subsumes
brick 21's vertex-degree bound as the `T = {j}` case.)

* `twoCellPartition` — the partition `{T, Tᶜ}` of a proper nonempty subset;
* `edgeCrosses` / `borderEdges` / `headBorderEdges` / `cutDeficiency` — named cut-count
  objects for the Frank reorientation campaign;
* `wpc_border_ge` — **the cut supply**: `k ≤ #{i | eᵢ touches both T and Tᶜ}`;
* `edgeCrosses_inter_union_indicator_le` and `borderEdges_card_inter_add_union_le` — the
  submodularity brick for the border count;
* `exists_border_head_outside_of_deficient_cut` — a deficient cut has an unclaimed border
  edge whose head is outside the cut;
* `exists_updateHead_decreases_positive_deficiency_cut` — updating such an edge into the
  cut strictly decreases that cut's positive deficiency.
-/

open Finset

namespace AGL24

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A single edge crosses the cut `T` when it touches `T` and is not contained in `T`. -/
def edgeCrosses (E T : Finset V) : Prop :=
  (E ∩ T).Nonempty ∧ ¬ E ⊆ T

/-- The `0/1` indicator for a single edge crossing a cut. -/
noncomputable def edgeCrossesIndicator (E T : Finset V) : ℕ := by
  classical
  exact if edgeCrosses E T then 1 else 0

omit [Fintype V] in
theorem edgeCrossesIndicator_eq (E T : Finset V) :
    edgeCrossesIndicator E T = if (E ∩ T).Nonempty ∧ ¬ E ⊆ T then 1 else 0 := by
  classical
  by_cases h : (E ∩ T).Nonempty ∧ ¬ E ⊆ T <;> simp [edgeCrossesIndicator, edgeCrosses, h]

/-- The edges crossing the cut `T`: they touch `T` and are not contained in `T`. -/
def borderEdges {ι : Type*} [Fintype ι] (e : ι → Finset V) (T : Finset V) : Finset ι :=
  Finset.univ.filter (fun i => (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T)

/-- The cut-crossing edges whose current orientation head lies in `T`. -/
def headBorderEdges {ι : Type*} [Fintype ι] {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) : Finset ι :=
  Finset.univ.filter (fun i => O.head i ∈ T ∧ ¬ e i ⊆ T)

/-- The positive part of the missing head-border count for a Frank cut. -/
def cutDeficiency {ι : Type*} [Fintype ι] {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) (k : ℕ) : ℕ :=
  k - (headBorderEdges O T).card

omit [Fintype V] in
@[simp] theorem mem_borderEdges {ι : Type*} [Fintype ι] (e : ι → Finset V)
    (T : Finset V) (i : ι) :
    i ∈ borderEdges e T ↔ edgeCrosses (e i) T := by
  simp [borderEdges, edgeCrosses]

omit [Fintype V] in
@[simp] theorem mem_headBorderEdges {ι : Type*} [Fintype ι] {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) (i : ι) :
    i ∈ headBorderEdges O T ↔ O.head i ∈ T ∧ ¬ e i ⊆ T := by
  simp [headBorderEdges]

omit [Fintype V] in
theorem headBorderEdges_subset_borderEdges {ι : Type*} [Fintype ι] {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) (hne : ∀ i, (e i).Nonempty) :
    headBorderEdges O T ⊆ borderEdges e T := by
  intro i hi
  rw [mem_headBorderEdges] at hi
  rw [mem_borderEdges, edgeCrosses]
  exact ⟨⟨O.head i, Finset.mem_inter.mpr ⟨O.head_mem i (hne i), hi.1⟩⟩, hi.2⟩

omit [Fintype V] in
theorem headBorderEdges_card_le_borderEdges_card {ι : Type*} [Fintype ι] {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) (hne : ∀ i, (e i).Nonempty) :
    (headBorderEdges O T).card ≤ (borderEdges e T).card :=
  Finset.card_le_card (headBorderEdges_subset_borderEdges O T hne)

omit [Fintype V] in
theorem cutDeficiency_pos_iff {ι : Type*} [Fintype ι] {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) (k : ℕ) :
    0 < cutDeficiency O T k ↔ (headBorderEdges O T).card < k := by
  rw [cutDeficiency, Nat.sub_pos_iff_lt]

omit [Fintype V] in
theorem cutDeficiency_eq_zero_of_le {ι : Type*} [Fintype ι] {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) {k : ℕ}
    (h : k ≤ (headBorderEdges O T).card) :
    cutDeficiency O T k = 0 := by
  rw [cutDeficiency, Nat.sub_eq_zero_of_le h]

omit [Fintype V] in
theorem mem_headBorderEdges_updateHead_iff {ι : Type*} [Fintype ι] {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) {i₀ : ι} {v : V}
    (hv : v ∈ e i₀) (hvT : v ∈ T) (hnotSub : ¬ e i₀ ⊆ T) (j : ι) :
    j ∈ headBorderEdges (O.updateHead i₀ v hv) T ↔
      j = i₀ ∨ j ∈ headBorderEdges O T := by
  classical
  by_cases hji : j = i₀
  · subst hji
    rw [mem_headBorderEdges]
    simp [HeadOrientation.updateHead, hnotSub, hvT]
  · simp [headBorderEdges, hji]

omit [Fintype V] in
theorem headBorderEdges_card_updateHead_eq_succ {ι : Type*} [Fintype ι]
    {e : ι → Finset V} (O : HeadOrientation e) (T : Finset V) {i₀ : ι} {v : V}
    (hv : v ∈ e i₀) (hvT : v ∈ T) (hnotSub : ¬ e i₀ ⊆ T)
    (hhead : O.head i₀ ∉ T) :
    (headBorderEdges (O.updateHead i₀ v hv) T).card =
      (headBorderEdges O T).card + 1 := by
  classical
  have hnotMem : i₀ ∉ headBorderEdges O T := by
    rw [mem_headBorderEdges]
    exact fun h => hhead h.1
  have hset : headBorderEdges (O.updateHead i₀ v hv) T =
      insert i₀ (headBorderEdges O T) := by
    ext j
    rw [mem_headBorderEdges_updateHead_iff O T hv hvT hnotSub j]
    simp [Finset.mem_insert]
  rw [hset, Finset.card_insert_of_notMem hnotMem]

omit [Fintype V] in
theorem cutDeficiency_updateHead_lt {ι : Type*} [Fintype ι]
    {e : ι → Finset V} (O : HeadOrientation e) (T : Finset V) {i₀ : ι} {v : V}
    {k : ℕ} (hv : v ∈ e i₀) (hvT : v ∈ T) (hnotSub : ¬ e i₀ ⊆ T)
    (hhead : O.head i₀ ∉ T) (hdef : (headBorderEdges O T).card < k) :
    cutDeficiency (O.updateHead i₀ v hv) T k < cutDeficiency O T k := by
  have hcard := headBorderEdges_card_updateHead_eq_succ O T hv hvT hnotSub hhead
  rw [cutDeficiency, cutDeficiency, hcard]
  omega

omit [Fintype V] in
theorem edgeCrosses_iff_exists_in_out (E T : Finset V) :
    edgeCrosses E T ↔
      (∃ x, x ∈ E ∧ x ∈ T) ∧ ∃ y, y ∈ E ∧ y ∉ T := by
  classical
  unfold edgeCrosses
  constructor
  · rintro ⟨⟨x, hx⟩, hnot⟩
    rw [Finset.mem_inter] at hx
    refine ⟨⟨x, hx.1, hx.2⟩, ?_⟩
    by_contra hall
    push Not at hall
    exact hnot (fun y hy => hall y hy)
  · rintro ⟨⟨x, hxE, hxT⟩, ⟨y, hyE, hyT⟩⟩
    exact ⟨⟨x, Finset.mem_inter.mpr ⟨hxE, hxT⟩⟩, fun hsub => hyT (hsub hyE)⟩

omit [Fintype V] in
theorem edgeCrosses_inter_imp_left_or_right (E A B : Finset V) :
    edgeCrosses E (A ∩ B) → edgeCrosses E A ∨ edgeCrosses E B := by
  classical
  rw [edgeCrosses_iff_exists_in_out, edgeCrosses_iff_exists_in_out,
    edgeCrosses_iff_exists_in_out]
  rintro ⟨⟨x, hxE, hxAB⟩, ⟨y, hyE, hyAB⟩⟩
  rw [Finset.mem_inter] at hxAB
  rw [Finset.mem_inter] at hyAB
  by_cases hyA : y ∈ A
  · right
    exact ⟨⟨x, hxE, hxAB.2⟩, ⟨y, hyE, fun hyB => hyAB ⟨hyA, hyB⟩⟩⟩
  · left
    exact ⟨⟨x, hxE, hxAB.1⟩, ⟨y, hyE, hyA⟩⟩

omit [Fintype V] in
theorem edgeCrosses_union_imp_left_or_right (E A B : Finset V) :
    edgeCrosses E (A ∪ B) → edgeCrosses E A ∨ edgeCrosses E B := by
  classical
  rw [edgeCrosses_iff_exists_in_out, edgeCrosses_iff_exists_in_out,
    edgeCrosses_iff_exists_in_out]
  rintro ⟨⟨x, hxE, hxAB⟩, ⟨y, hyE, hyAB⟩⟩
  rw [Finset.mem_union] at hxAB
  rw [Finset.mem_union] at hyAB
  rcases hxAB with hxA | hxB
  · left
    exact ⟨⟨x, hxE, hxA⟩, ⟨y, hyE, fun hyA => hyAB (Or.inl hyA)⟩⟩
  · right
    exact ⟨⟨x, hxE, hxB⟩, ⟨y, hyE, fun hyB => hyAB (Or.inr hyB)⟩⟩

omit [Fintype V] in
theorem not_edgeCrosses_left_not_both (E A B : Finset V)
    (hA : ¬ edgeCrosses E A) :
    ¬ (edgeCrosses E (A ∩ B) ∧ edgeCrosses E (A ∪ B)) := by
  classical
  rw [edgeCrosses_iff_exists_in_out] at hA
  rintro ⟨hinter, hunion⟩
  rw [edgeCrosses_iff_exists_in_out] at hinter hunion
  rcases hinter with ⟨⟨x, hxE, hxAB⟩, -⟩
  rcases hunion with ⟨-, ⟨y, hyE, hyAB⟩⟩
  rw [Finset.mem_inter] at hxAB
  rw [Finset.mem_union] at hyAB
  exact hA ⟨⟨x, hxE, hxAB.1⟩, ⟨y, hyE, fun hyA => hyAB (Or.inl hyA)⟩⟩

private theorem bool_sum_le_two (p q : Prop) [Decidable p] [Decidable q] :
    (if p then 1 else 0) + (if q then 1 else 0) ≤ 2 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

private theorem bool_sum_le_one_of_not_and (p q : Prop) [Decidable p] [Decidable q]
    (h : ¬ (p ∧ q)) :
    (if p then 1 else 0) + (if q then 1 else 0) ≤ 1 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] at h ⊢

omit [Fintype V] in
/-- Pointwise submodularity for the `0/1` edge-crossing indicator. -/
theorem edgeCrosses_inter_union_indicator_le (E A B : Finset V) :
    edgeCrossesIndicator E (A ∩ B) + edgeCrossesIndicator E (A ∪ B)
      ≤ edgeCrossesIndicator E A + edgeCrossesIndicator E B := by
  classical
  unfold edgeCrossesIndicator
  by_cases hA : edgeCrosses E A
  · by_cases hB : edgeCrosses E B
    · have hleft := bool_sum_le_two (edgeCrosses E (A ∩ B)) (edgeCrosses E (A ∪ B))
      simpa [hA, hB] using hleft
    · have hnotboth := not_edgeCrosses_left_not_both E B A hB
      have hleft : (if edgeCrosses E (A ∩ B) then 1 else 0) +
          (if edgeCrosses E (A ∪ B) then 1 else 0) ≤ 1 := by
        rw [Finset.inter_comm A B, Finset.union_comm A B]
        exact bool_sum_le_one_of_not_and _ _ hnotboth
      simpa [hA, hB] using hleft
  · by_cases hB : edgeCrosses E B
    · have hnotboth := not_edgeCrosses_left_not_both E A B hA
      have hleft : (if edgeCrosses E (A ∩ B) then 1 else 0) +
          (if edgeCrosses E (A ∪ B) then 1 else 0) ≤ 1 :=
        bool_sum_le_one_of_not_and _ _ hnotboth
      simpa [hA, hB] using hleft
    · have hInter : ¬ edgeCrosses E (A ∩ B) := by
        intro h
        rcases edgeCrosses_inter_imp_left_or_right E A B h with h' | h'
        · exact hA h'
        · exact hB h'
      have hUnion : ¬ edgeCrosses E (A ∪ B) := by
        intro h
        rcases edgeCrosses_union_imp_left_or_right E A B h with h' | h'
        · exact hA h'
        · exact hB h'
      simp [hInter, hUnion]

/-- The two-cell partition `{T, univ \ T}` of a proper nonempty subset `T`. -/
def twoCellPartition (T : Finset V) (hT : T.Nonempty) (hTne : T ≠ Finset.univ) :
    Finpartition (Finset.univ : Finset V) where
  parts := {T, Finset.univ \ T}
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro c₁ hc₁ c₂ hc₂ hne
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hc₁ hc₂
    rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl
    · exact absurd rfl hne
    · exact Finset.disjoint_sdiff
    · exact Finset.sdiff_disjoint
    · exact absurd rfl hne
  sup_parts := by
    rw [Finset.sup_insert, Finset.sup_singleton]
    rw [Finset.sup_eq_union]
    show id T ∪ id (Finset.univ \ T) = Finset.univ
    rw [id, id]
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ T)]
  bot_notMem := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push Not
    constructor
    · intro h
      obtain ⟨x, hx⟩ := hT
      rw [← h] at hx
      exact absurd hx (Finset.notMem_empty x)
    · intro h
      obtain ⟨x, hx⟩ : ∃ x, x ∉ T := by
        by_contra hall
        push Not at hall
        exact hTne (Finset.eq_univ_iff_forall.mpr hall)
      have : x ∈ Finset.univ \ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
      rw [← h] at this
      exact absurd this (Finset.notMem_empty x)

/-- **The cut supply** (the necessary side of Frank's orientation theorem): every proper
nonempty vertex subset of a `k`-weakly-partition-connected family is crossed by at least `k`
edges. -/
theorem wpc_border_ge {ι : Type*} [Fintype ι] {k : ℕ}
    (e : ι → Finset V) (T : Finset V) (hT : T.Nonempty) (hTne : T ≠ Finset.univ)
    (h : WeaklyPartitionConnected k (Finset.univ : Finset V) e) :
    k ≤ (borderEdges e T).card := by
  classical
  have hP := h (twoCellPartition T hT hTne)
  -- The partition has two parts.
  have hTT : T ≠ Finset.univ \ T := by
    intro heq
    obtain ⟨x, hx⟩ := hT
    have := heq ▸ hx
    exact absurd hx (Finset.mem_sdiff.mp this).2
  have hcard : (twoCellPartition T hT hTne).parts.card = 2 := by
    unfold twoCellPartition
    rw [Finset.card_insert_of_notMem (by
      rw [Finset.mem_singleton]
      exact hTT), Finset.card_singleton]
  rw [hcard] at hP
  -- Per edge: touched − 1 ≤ border indicator.
  have hper : ∀ i, (touchedCells (twoCellPartition T hT hTne) (e i ∩ Finset.univ)).card - 1
      ≤ (if (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T then 1 else 0) := by
    intro i
    by_cases hborder : (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T
    · rw [if_pos hborder]
      have : (touchedCells (twoCellPartition T hT hTne) (e i ∩ Finset.univ)).card ≤ 2 := by
        refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
        rw [hcard]
      omega
    · rw [if_neg hborder]
      rw [not_and_or] at hborder
      -- The edge misses one of the two cells: at most one touched cell.
      have hsub : ∃ c₀ : Finset V,
          touchedCells (twoCellPartition T hT hTne) (e i ∩ Finset.univ) ⊆ {c₀} := by
        rcases hborder with hmiss | hsub
        · -- e i misses T: only the complement cell can be touched.
          refine ⟨Finset.univ \ T, fun c hc => ?_⟩
          unfold touchedCells at hc
          rw [Finset.mem_filter] at hc
          obtain ⟨hcparts, x, hx⟩ := hc
          unfold twoCellPartition at hcparts
          rw [Finset.mem_insert, Finset.mem_singleton] at hcparts
          rcases hcparts with rfl | rfl
          · exfalso
            apply hmiss
            rw [Finset.mem_inter, Finset.mem_inter] at hx
            exact ⟨x, Finset.mem_inter.mpr ⟨hx.1.1, hx.2⟩⟩
          · exact Finset.mem_singleton_self _
        · -- e i ⊆ T: only the T cell can be touched.
          rw [not_not] at hsub
          refine ⟨T, fun c hc => ?_⟩
          unfold touchedCells at hc
          rw [Finset.mem_filter] at hc
          obtain ⟨hcparts, x, hx⟩ := hc
          unfold twoCellPartition at hcparts
          rw [Finset.mem_insert, Finset.mem_singleton] at hcparts
          rcases hcparts with rfl | rfl
          · exact Finset.mem_singleton_self _
          · exfalso
            rw [Finset.mem_inter, Finset.mem_inter] at hx
            obtain ⟨⟨hxe, -⟩, hxc⟩ := hx
            exact (Finset.mem_sdiff.mp hxc).2 (hsub hxe)
      obtain ⟨c₀, hc₀⟩ := hsub
      have := Finset.card_le_card hc₀
      rw [Finset.card_singleton] at this
      omega
  calc k = k * (2 - 1) := by omega
  _ ≤ ∑ i, ((touchedCells (twoCellPartition T hT hTne) (e i ∩ Finset.univ)).card - 1) := hP
  _ ≤ ∑ i, (if (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T then 1 else 0) :=
      Finset.sum_le_sum fun i _ => hper i
  _ = (borderEdges e T).card := by
      rw [borderEdges, Finset.card_filter]

omit [Fintype V] in
/-- Submodularity of the hypergraph border-count cut function. This is the F2 uncrossing
bookkeeping brick: the pointwise `0/1` edge-crossing submodularity summed over all edges. -/
theorem borderEdges_card_inter_add_union_le {ι : Type*} [Fintype ι]
    (e : ι → Finset V) (A B : Finset V) :
    (borderEdges e (A ∩ B)).card + (borderEdges e (A ∪ B)).card
      ≤ (borderEdges e A).card + (borderEdges e B).card := by
  classical
  simp only [borderEdges, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    rw [← edgeCrossesIndicator_eq (e i) (A ∩ B),
      ← edgeCrossesIndicator_eq (e i) (A ∪ B),
      ← edgeCrossesIndicator_eq (e i) A,
      ← edgeCrossesIndicator_eq (e i) B]
    exact edgeCrosses_inter_union_indicator_le (e i) A B

omit [Fintype V] in
/-- If the head-border count is strictly smaller than the full border count, some border edge
has not yet been headed into the cut. -/
theorem exists_border_not_head_of_headBorder_lt_border {ι : Type*} [Fintype ι]
    {e : ι → Finset V} (O : HeadOrientation e) (T : Finset V)
    (hlt : (headBorderEdges O T).card < (borderEdges e T).card) :
    ∃ i, i ∈ borderEdges e T ∧ i ∉ headBorderEdges O T := by
  classical
  by_contra h
  push Not at h
  have hsub : borderEdges e T ⊆ headBorderEdges O T := by
    intro i hi
    exact h i hi
  have := Finset.card_le_card hsub
  omega

/-- A strictly deficient proper WPC cut has a crossing edge whose head lies outside the cut.
This is the immediate F1 supply consumed by later Frank reorientation/uncrossing steps. -/
theorem exists_border_head_outside_of_deficient_cut {ι : Type*} [Fintype ι]
    {k : ℕ} {e : ι → Finset V} (O : HeadOrientation e) (T : Finset V)
    (hT : T.Nonempty) (hTne : T ≠ Finset.univ)
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset V) e)
    (hdef : (headBorderEdges O T).card < k) :
    ∃ i, (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T ∧ O.head i ∉ T := by
  classical
  have hborder : k ≤ (borderEdges e T).card := wpc_border_ge e T hT hTne hwpc
  obtain ⟨i, hiborder, hihead⟩ :=
    exists_border_not_head_of_headBorder_lt_border O T (lt_of_lt_of_le hdef hborder)
  rw [mem_borderEdges] at hiborder
  rw [mem_headBorderEdges] at hihead
  refine ⟨i, hiborder.1, hiborder.2, ?_⟩
  intro hhead
  exact hihead ⟨hhead, hiborder.2⟩

/-- Positive `cutDeficiency` form of `exists_border_head_outside_of_deficient_cut`. -/
theorem exists_border_head_outside_of_positive_deficiency {ι : Type*} [Fintype ι]
    {k : ℕ} {e : ι → Finset V} (O : HeadOrientation e) (T : Finset V)
    (hT : T.Nonempty) (hTne : T ≠ Finset.univ)
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset V) e)
    (hdef : 0 < cutDeficiency O T k) :
    ∃ i, (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T ∧ O.head i ∉ T := by
  exact exists_border_head_outside_of_deficient_cut O T hT hTne hwpc
    ((cutDeficiency_pos_iff O T k).mp hdef)

omit [Fintype V] in
theorem exists_updateHead_decreases_cutDeficiency_of_border_head_outside
    {ι : Type*} [Fintype ι] {k : ℕ} {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) {i₀ : ι}
    (hitouch : (e i₀ ∩ T).Nonempty) (hnotSub : ¬ e i₀ ⊆ T)
    (hhead : O.head i₀ ∉ T) (hdef : (headBorderEdges O T).card < k) :
    ∃ O' : HeadOrientation e,
      (headBorderEdges O' T).card = (headBorderEdges O T).card + 1 ∧
        cutDeficiency O' T k < cutDeficiency O T k := by
  obtain ⟨v, hv⟩ := hitouch
  rw [Finset.mem_inter] at hv
  exact ⟨O.updateHead i₀ v hv.1,
    headBorderEdges_card_updateHead_eq_succ O T hv.1 hv.2 hnotSub hhead,
    cutDeficiency_updateHead_lt O T hv.1 hv.2 hnotSub hhead hdef⟩

/-- Positive-deficiency local reorientation step for a single cut. This is only the F3
one-cut decrease brick; it does not assert that other cuts remain nondeficient or prove
termination. -/
theorem exists_updateHead_decreases_positive_deficiency_cut {ι : Type*} [Fintype ι]
    {k : ℕ} {e : ι → Finset V} (O : HeadOrientation e) (T : Finset V)
    (hT : T.Nonempty) (hTne : T ≠ Finset.univ)
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset V) e)
    (hdef : 0 < cutDeficiency O T k) :
    ∃ O' : HeadOrientation e,
      (headBorderEdges O' T).card = (headBorderEdges O T).card + 1 ∧
        cutDeficiency O' T k < cutDeficiency O T k := by
  have hlt : (headBorderEdges O T).card < k := (cutDeficiency_pos_iff O T k).mp hdef
  obtain ⟨i, hitouch, hnotSub, hhead⟩ :=
    exists_border_head_outside_of_deficient_cut O T hT hTne hwpc hlt
  exact exists_updateHead_decreases_cutDeficiency_of_border_head_outside
    O T hitouch hnotSub hhead hlt

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.wpc_border_ge
#print axioms AGL24.borderEdges_card_inter_add_union_le
#print axioms AGL24.exists_border_head_outside_of_positive_deficiency
#print axioms AGL24.exists_updateHead_decreases_positive_deficiency_cut
