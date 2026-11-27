/-
Copyright (c) 2026 Spuddya7x. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Spuddya7x
-/

import ArkLib.Data.CodingTheory.AGL24FrankDescent

/-!
# [AGL24] Theorem A.3: Frank's rooted orientation theorem, unconditionally

This file proves Frank's orientation theorem for weakly partition-connected hypergraphs
(Theorem A.3 of [AGL24], the appendix's combinatorial input) and thereby discharges the named
residual `AGL24.FrankUncrossingResidual` with no extra hypotheses. Through the existing descent
and out-cut glue of `AGL24FrankDescent`/`AGL24FrankInterface`, this also proves
`FrankRootedOutCutTheorem` and `FrankOrientationResidual` outright.

## Strategy

The proof does not perform the single-reorientation descent that the residual's name suggests.
Instead it produces an orientation of total root deficiency `0`, which then beats every
positive-potential orientation. The argument is the classical in-degree-vector proof:

1. **Only in-degrees matter.** For a root cut `T` with complement `X`, every edge touching `X`
   either has its head in `X` or crosses `T` with its head in `T`. Hence the head-border count
   of `T` is at least `touchCount e X - #{i | head i ∈ X}`. So it suffices to find an
   orientation whose in-degree vector `m` satisfies `m(X) + k ≤ touchCount e X` for every
   nonempty `X` avoiding the root.
2. **A maximal feasible vector.** Call `m : V → ℕ` *feasible* when
   `m(X) + req X ≤ touchCount e X` for every `X`, where `req X = k` for nonempty root-free `X`
   and `0` otherwise. `touchCount` is submodular and `req` is supermodular on intersecting
   pairs, so *tight* sets are closed under unions of intersecting pairs. Take a feasible `m` of
   maximal total mass: every vertex then lies in a tight set, and the maximal tight sets form a
   partition `P` of the vertex set.
3. **Counting on the tight partition.** Summing tightness over `P` gives
   `m(V) + k(|P| - 1) = ∑_i |P(eᵢ)|`, and weak partition-connectivity on `P` gives
   `∑_i (|P(eᵢ)| - 1) ≥ k(|P| - 1)`, so `m(V) ≥ |E|` (edges are nonempty).
4. **Hall's theorem.** Feasibility at complements of edge-unions gives Hall's condition for
   assigning each edge a distinct *slot* `(v, j)` with `v ∈ eᵢ` and `j < m v`
   (`Finset.all_card_le_biUnion_card_iff_exists_injective`). The resulting orientation has
   in-degree at most `m`, hence zero deficiency on every proper root cut by step 1.

The statement is the one [AGL24] imports from Frank, Király and Király (2003); see the
`AGL24Orientation` module docstring for its role in Corollary A.4.

## Main results

* `AGL24.FrankOrientation.exists_totalRootDeficiency_eq_zero` — every `k`-weakly
  partition-connected family of nonempty edges has, for every root, an orientation of total
  root deficiency `0`.
* `AGL24.frankUncrossingResidual_holds` — `FrankUncrossingResidual ι k` for every `k`.
* `AGL24.frankRootedOutCutTheorem_holds`, `AGL24.frankOrientationResidual_holds` — the
  downstream interfaces, now unconditional.
-/

open Finset

namespace AGL24

namespace FrankOrientation

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-! ### Touch counts and the root requirement -/

/-- The number of edges meeting the vertex set `X`. -/
def touchCount (e : ι → Finset V) (X : Finset V) : ℕ :=
  #{i | (e i ∩ X).Nonempty}

/-- The rooted requirement: `k` on nonempty vertex sets avoiding the root, `0` otherwise. -/
def req (r : V) (k : ℕ) (X : Finset V) : ℕ :=
  if X.Nonempty ∧ r ∉ X then k else 0

omit [DecidableEq ι] [Fintype V] in
theorem touchCount_le_card (e : ι → Finset V) (X : Finset V) :
    touchCount e X ≤ Fintype.card ι :=
  (card_filter_le _ _).trans_eq card_univ

omit [DecidableEq ι] [Fintype V] in
/-- `touchCount` is submodular. -/
theorem touchCount_union_add_inter_le (e : ι → Finset V) (X Y : Finset V) :
    touchCount e (X ∪ Y) + touchCount e (X ∩ Y) ≤ touchCount e X + touchCount e Y := by
  classical
  unfold touchCount
  rw [← card_union_add_card_inter ({i | (e i ∩ X).Nonempty} : Finset ι)]
  refine add_le_add (card_le_card fun i hi => ?_) (card_le_card fun i hi => ?_)
  · simp only [mem_filter, mem_univ, true_and, mem_union] at hi ⊢
    obtain ⟨x, hx⟩ := hi
    rw [mem_inter, mem_union] at hx
    rcases hx.2 with h | h
    · exact Or.inl ⟨x, mem_inter.2 ⟨hx.1, h⟩⟩
    · exact Or.inr ⟨x, mem_inter.2 ⟨hx.1, h⟩⟩
  · simp only [mem_filter, mem_univ, true_and, mem_inter] at hi ⊢
    obtain ⟨x, hx⟩ := hi
    rw [mem_inter, mem_inter] at hx
    exact ⟨⟨x, mem_inter.2 ⟨hx.1, hx.2.1⟩⟩, ⟨x, mem_inter.2 ⟨hx.1, hx.2.2⟩⟩⟩

omit [Fintype V] in
/-- The requirement is supermodular on intersecting pairs. -/
theorem req_add_le_of_inter_nonempty (r : V) (k : ℕ) {X Y : Finset V}
    (h : (X ∩ Y).Nonempty) :
    req r k X + req r k Y ≤ req r k (X ∪ Y) + req r k (X ∩ Y) := by
  have hX : X.Nonempty := h.mono inter_subset_left
  have hY : Y.Nonempty := h.mono inter_subset_right
  have hU : (X ∪ Y).Nonempty := hX.mono subset_union_left
  unfold req
  by_cases hrX : r ∈ X <;> by_cases hrY : r ∈ Y <;>
    simp [hrX, hrY, hX, hY, hU, h, mem_union, mem_inter]

/-! ### Feasible in-degree vectors and tight sets -/

/-- A candidate in-degree vector `m` is feasible when every vertex set `X` satisfies
`m(X) + req X ≤ touchCount e X`. -/
def Feasible (e : ι → Finset V) (r : V) (k : ℕ) (m : V → ℕ) : Prop :=
  ∀ X : Finset V, (∑ v ∈ X, m v) + req r k X ≤ touchCount e X

/-- A vertex set is tight for `m` when its feasibility inequality is an equality. -/
def Tight (e : ι → Finset V) (r : V) (k : ℕ) (m : V → ℕ) (X : Finset V) : Prop :=
  (∑ v ∈ X, m v) + req r k X = touchCount e X

omit [DecidableEq ι] [Fintype V] in
/-- Tight sets with a common vertex have a tight union. -/
theorem tight_union {e : ι → Finset V} {r : V} {k : ℕ} {m : V → ℕ}
    (hm : Feasible e r k m) {X Y : Finset V} (hX : Tight e r k m X) (hY : Tight e r k m Y)
    (h : (X ∩ Y).Nonempty) : Tight e r k m (X ∪ Y) := by
  have hs : ∑ v ∈ X ∪ Y, m v + ∑ v ∈ X ∩ Y, m v = ∑ v ∈ X, m v + ∑ v ∈ Y, m v :=
    sum_union_inter
  have h1 := hm (X ∪ Y)
  have h2 := hm (X ∩ Y)
  have h3 := touchCount_union_add_inter_le e X Y
  have h4 := req_add_le_of_inter_nonempty r k h
  unfold Tight at hX hY ⊢
  omega

omit [DecidableEq ι] [Fintype V] in
/-- The supremum of a nonempty family of tight sets sharing a vertex `v` is tight and
contains `v`. -/
theorem tight_sup {e : ι → Finset V} {r : V} {k : ℕ} {m : V → ℕ} (hm : Feasible e r k m)
    (v : V) (𝒮 : Finset (Finset V)) (hne : 𝒮.Nonempty)
    (h𝒮 : ∀ X ∈ 𝒮, v ∈ X ∧ Tight e r k m X) :
    v ∈ 𝒮.sup id ∧ Tight e r k m (𝒮.sup id) := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h𝒮 a (mem_singleton_self a)
  | cons a s ha hs ih =>
    obtain ⟨hva, hta⟩ := h𝒮 a (mem_cons_self a s)
    obtain ⟨hvs, hts⟩ := ih fun X hX => h𝒮 X (mem_cons.2 (Or.inr hX))
    rw [sup_cons]
    exact ⟨mem_union_left _ hva, tight_union hm hta hts ⟨v, mem_inter.2 ⟨hva, hvs⟩⟩⟩

omit [DecidableEq ι] [Fintype V] in
/-- If `0` is feasible, some feasible vector has every vertex inside a tight set. -/
theorem exists_feasible_forall_mem_tight [Finite V] {e : ι → Finset V} {r : V} {k : ℕ}
    (h0 : Feasible e r k 0) :
    ∃ m, Feasible e r k m ∧ ∀ v, ∃ X, v ∈ X ∧ Tight e r k m X := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let S : Finset (V → ℕ) :=
    (Fintype.piFinset fun _ : V => range (Fintype.card ι + 1)).filter (Feasible e r k)
  have h0S : (0 : V → ℕ) ∈ S := by
    refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun v => ?_, h0⟩
    simp
  obtain ⟨m, hmS, hmax⟩ := S.exists_max_image (fun m => ∑ v, m v) ⟨0, h0S⟩
  have hm : Feasible e r k m := (mem_filter.1 hmS).2
  refine ⟨m, hm, fun v => ?_⟩
  by_contra hcon
  push Not at hcon
  let m' : V → ℕ := m + Pi.single v 1
  have hsum : ∀ X : Finset V, ∑ w ∈ X, m' w = ∑ w ∈ X, m w + if v ∈ X then 1 else 0 := by
    intro X
    simp [m', sum_add_distrib, sum_pi_single']
  have hm' : Feasible e r k m' := by
    intro X
    rw [hsum X]
    have hX := hm X
    split_ifs with hv
    · have hnt := hcon X hv
      unfold Tight at hnt
      omega
    · omega
  have hmem : m' ∈ S := by
    refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun w => ?_, hm'⟩
    have hw := hm' {w}
    rw [sum_singleton] at hw
    have := touchCount_le_card e {w}
    rw [mem_range]
    omega
  have hle := hmax m' hmem
  have hs := hsum univ
  simp only [mem_univ, ite_true] at hs
  omega

/-! ### The closure of a vertex and the tight partition -/

section Closure

variable (e : ι → Finset V) (r : V) (k : ℕ) (m : V → ℕ)

/-- The union of all tight sets containing `v`. -/
noncomputable def tightClosure (v : V) : Finset V := by
  classical
  exact ({X | v ∈ X ∧ Tight e r k m X} : Finset (Finset V)).sup id

variable {e r k m}

omit [DecidableEq ι] in
theorem mem_tightClosure_self_and_tight (hm : Feasible e r k m)
    (hblock : ∀ v, ∃ X, v ∈ X ∧ Tight e r k m X) (v : V) :
    v ∈ tightClosure e r k m v ∧ Tight e r k m (tightClosure e r k m v) := by
  classical
  obtain ⟨X, hvX, hX⟩ := hblock v
  unfold tightClosure
  convert tight_sup hm v ({X | v ∈ X ∧ Tight e r k m X} : Finset (Finset V))
    ⟨X, by simp [hvX, hX]⟩ (fun Y hY => by simpa using hY) using 2

omit [DecidableEq ι] in
theorem subset_tightClosure {v : V} {X : Finset V} (hvX : v ∈ X) (hX : Tight e r k m X) :
    X ⊆ tightClosure e r k m v := by
  classical
  unfold tightClosure
  convert le_sup (f := id) (s := ({X | v ∈ X ∧ Tight e r k m X} : Finset (Finset V)))
    (mem_filter.2 ⟨mem_univ X, hvX, hX⟩) using 1
  rfl

omit [DecidableEq ι] in
theorem tightClosure_eq_of_mem (hm : Feasible e r k m)
    (hblock : ∀ v, ∃ X, v ∈ X ∧ Tight e r k m X) {v w : V}
    (hw : w ∈ tightClosure e r k m v) :
    tightClosure e r k m w = tightClosure e r k m v := by
  obtain ⟨hvv, htv⟩ := mem_tightClosure_self_and_tight hm hblock v
  obtain ⟨hww, htw⟩ := mem_tightClosure_self_and_tight hm hblock w
  have hvw : tightClosure e r k m v ⊆ tightClosure e r k m w := subset_tightClosure hw htv
  have hunion : Tight e r k m (tightClosure e r k m w ∪ tightClosure e r k m v) :=
    tight_union hm htw htv ⟨w, mem_inter.2 ⟨hww, hw⟩⟩
  have hwv : tightClosure e r k m w ∪ tightClosure e r k m v ⊆ tightClosure e r k m v :=
    subset_tightClosure (mem_union_right _ hvv) hunion
  exact le_antisymm (subset_union_left.trans hwv) hvw

/-- The maximal tight sets form a partition of the vertex set. -/
noncomputable def tightPartition (hm : Feasible e r k m)
    (hblock : ∀ v, ∃ X, v ∈ X ∧ Tight e r k m X) : Finpartition (univ : Finset V) where
  parts := univ.image (tightClosure e r k m)
  supIndep := by
    rw [supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hab
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at ha hb
    obtain ⟨v, rfl⟩ := ha
    obtain ⟨w, rfl⟩ := hb
    refine disjoint_left.2 fun x hxv hxw => hab ?_
    exact (tightClosure_eq_of_mem hm hblock hxv).symm.trans
      (tightClosure_eq_of_mem hm hblock hxw)
  sup_parts := by
    rw [sup_image]
    ext x
    simp only [mem_univ, iff_true]
    exact mem_sup.2 ⟨x, mem_univ x, (mem_tightClosure_self_and_tight hm hblock x).1⟩
  bot_notMem := by
    simp only [bot_eq_empty, mem_image, mem_univ, true_and, not_exists]
    intro v hv
    have := (mem_tightClosure_self_and_tight hm hblock v).1
    rw [hv] at this
    exact notMem_empty v this

omit [DecidableEq ι] in
theorem tight_of_mem_tightPartition (hm : Feasible e r k m)
    (hblock : ∀ v, ∃ X, v ∈ X ∧ Tight e r k m X) {c : Finset V}
    (hc : c ∈ (tightPartition hm hblock).parts) : Tight e r k m c := by
  obtain ⟨v, -, rfl⟩ := mem_image.1 hc
  exact (mem_tightClosure_self_and_tight hm hblock v).2

end Closure

/-! ### Counting over a partition of the vertex set -/

omit [Fintype ι] [DecidableEq ι] in
theorem sum_parts_sum (P : Finpartition (univ : Finset V)) (f : V → ℕ) :
    ∑ c ∈ P.parts, ∑ v ∈ c, f v = ∑ v, f v := by
  have h := sum_biUnion (f := f) P.supIndep.pairwiseDisjoint
  simp only [id] at h
  rw [← h, P.biUnion_parts]

omit [DecidableEq ι] in
/-- Double counting of edge-cell incidences. -/
theorem sum_touchCount_parts (e : ι → Finset V) (P : Finpartition (univ : Finset V)) :
    ∑ c ∈ P.parts, touchCount e c = ∑ i, #(touchedCells P (e i ∩ univ)) := by
  simp only [touchCount, touchedCells, card_filter, inter_univ]
  exact sum_comm

omit [Fintype ι] [DecidableEq ι] in
/-- Exactly one part contains the root, so the requirements sum to `k (|P| - 1)`. -/
theorem sum_req_parts (r : V) (k : ℕ) (P : Finpartition (univ : Finset V)) :
    ∑ c ∈ P.parts, req r k c = k * (#P.parts - 1) := by
  have hroot : ({c ∈ P.parts | r ∈ c} : Finset (Finset V)) = {P.part r} := by
    ext c
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hc, hrc⟩
      exact (P.part_eq_of_mem hc hrc).symm
    · rintro rfl
      exact ⟨P.part_mem.2 (mem_univ r), P.mem_part_self.2 (mem_univ r)⟩
  have hsplit := card_filter_add_card_filter_not (s := P.parts) (fun c => r ∈ c)
  rw [hroot, card_singleton] at hsplit
  have hreq : ∀ c ∈ P.parts, req r k c = if r ∉ c then k else 0 := by
    intro c hc
    have hne : c.Nonempty := P.nonempty_of_mem_parts hc
    simp [req, hne]
  rw [sum_congr rfl hreq, sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul]
  rw [mul_comm]
  congr 1
  omega

omit [DecidableEq ι] in
/-- Each nonempty edge touches at least one part. -/
theorem one_le_card_touchedCells (P : Finpartition (univ : Finset V)) {E : Finset V}
    (hE : E.Nonempty) : 1 ≤ #(touchedCells P (E ∩ univ)) := by
  obtain ⟨x, hx⟩ := hE
  refine card_pos.2 ⟨P.part x, ?_⟩
  simp only [touchedCells, mem_filter, inter_univ]
  exact ⟨P.part_mem.2 (mem_univ x), x, mem_inter.2 ⟨hx, P.mem_part_self.2 (mem_univ x)⟩⟩

/-! ### Total mass of a blocked feasible vector -/

omit [DecidableEq ι] in
/-- A feasible vector whose every vertex lies in a tight set has total mass at least the
number of edges, provided the family is weakly partition-connected with nonempty edges. -/
theorem card_le_sum_of_blocked {e : ι → Finset V} {r : V} {k : ℕ} {m : V → ℕ}
    (hne : ∀ i, (e i).Nonempty) (hwpc : WeaklyPartitionConnected k (univ : Finset V) e)
    (hm : Feasible e r k m) (hblock : ∀ v, ∃ X, v ∈ X ∧ Tight e r k m X) :
    Fintype.card ι ≤ ∑ v, m v := by
  set P := tightPartition hm hblock
  have htight : ∑ c ∈ P.parts, ((∑ v ∈ c, m v) + req r k c) = ∑ c ∈ P.parts, touchCount e c :=
    sum_congr rfl fun c hc => tight_of_mem_tightPartition hm hblock hc
  rw [sum_add_distrib, sum_parts_sum, sum_req_parts, sum_touchCount_parts] at htight
  have hw := hwpc P
  have hone : ∑ i, #(touchedCells P (e i ∩ univ)) =
      ∑ i, (#(touchedCells P (e i ∩ univ)) - 1) + Fintype.card ι := by
    rw [← card_univ, card_eq_sum_ones, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => (Nat.sub_add_cancel (one_le_card_touchedCells P (hne i))).symm
  omega

/-! ### From a feasible vector to an orientation (Hall) -/

omit [DecidableEq ι] in
/-- Hall's theorem turns a feasible vector of total mass at least `|E|` into an orientation
whose in-degree on every vertex set is bounded by the vector. -/
theorem exists_orientation_inDegree_le {e : ι → Finset V} {r : V} {k : ℕ} {m : V → ℕ}
    (hm : Feasible e r k m) (hmass : Fintype.card ι ≤ ∑ v, m v) :
    ∃ O : HeadOrientation e, ∀ X : Finset V, #{i | O.head i ∈ X} ≤ ∑ v ∈ X, m v := by
  classical
  let slots : ι → Finset ((_ : V) × ℕ) := fun i => (e i).sigma fun v => range (m v)
  have hbi : ∀ s : Finset ι, s.biUnion slots = (s.biUnion e).sigma fun v => range (m v) := by
    intro s
    ext ⟨v, j⟩
    simp [slots, mem_biUnion, mem_sigma]
    tauto
  have hhall : ∀ s : Finset ι, #s ≤ #(s.biUnion slots) := by
    intro s
    rw [hbi, card_sigma]
    simp only [card_range]
    set W := s.biUnion e
    have hX := hm (univ \ W)
    have htouch : touchCount e (univ \ W) ≤ Fintype.card ι - #s := by
      unfold touchCount
      have hsub : ({i | (e i ∩ (univ \ W)).Nonempty} : Finset ι) ⊆ univ \ s := by
        intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi
        simp only [mem_sdiff, mem_univ, true_and]
        intro his
        obtain ⟨x, hx⟩ := hi
        rw [mem_inter, mem_sdiff] at hx
        exact hx.2.2 (mem_biUnion.2 ⟨i, his, hx.1⟩)
      exact (card_le_card hsub).trans_eq (card_univ_sdiff s)
    have hsplit : ∑ v ∈ W, m v + ∑ v ∈ univ \ W, m v = ∑ v, m v := by
      rw [add_comm, sum_sdiff (subset_univ W)]
    have hs : #s ≤ Fintype.card ι := card_le_univ s
    omega
  obtain ⟨f, hfinj, hf⟩ := (all_card_le_biUnion_card_iff_exists_injective slots).1 hhall
  have hfmem : ∀ i, (f i).1 ∈ e i ∧ (f i).2 < m (f i).1 := by
    intro i
    have := hf i
    simp only [slots, mem_sigma, mem_range] at this
    exact this
  refine ⟨⟨fun i => (f i).1, fun i _ => (hfmem i).1⟩, fun X => ?_⟩
  have hmaps : ∀ i ∈ ({i | (f i).1 ∈ X} : Finset ι), f i ∈ X.sigma fun v => range (m v) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [mem_sigma, mem_range]
    exact ⟨hi, (hfmem i).2⟩
  have := card_le_card_of_injOn f hmaps hfinj.injOn
  rw [card_sigma] at this
  simpa using this

/-! ### Zero root deficiency -/

omit [DecidableEq ι] in
/-- An orientation with in-degrees bounded by a feasible vector has every proper root cut
crossed by at least `k` head-border edges. -/
theorem le_card_headBorderEdges {e : ι → Finset V} {r : V} {k : ℕ} {m : V → ℕ}
    (hm : Feasible e r k m) (O : HeadOrientation e)
    (hO : ∀ X : Finset V, #{i | O.head i ∈ X} ≤ ∑ v ∈ X, m v)
    {T : Finset V} (hrT : r ∈ T) (hT : T ≠ univ) :
    k ≤ #(headBorderEdges O T) := by
  classical
  set X := univ \ T
  have hXne : X.Nonempty := by
    obtain ⟨x, -, hx⟩ :=
      Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨subset_univ T, hT⟩)
    exact ⟨x, mem_sdiff.2 ⟨mem_univ x, hx⟩⟩
  have hrX : r ∉ X := fun h => (mem_sdiff.1 h).2 hrT
  have hfeas := hm X
  have hreq : req r k X = k := by simp [req, hXne, hrX]
  rw [hreq] at hfeas
  have hcover : ({i | (e i ∩ X).Nonempty} : Finset ι) ⊆
      headBorderEdges O T ∪ ({i | O.head i ∈ X} : Finset ι) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    obtain ⟨x, hx⟩ := hi
    rw [mem_inter, mem_sdiff] at hx
    rw [mem_union, mem_headBorderEdges]
    by_cases hh : O.head i ∈ T
    · exact Or.inl ⟨hh, fun hsub => hx.2.2 (hsub hx.1)⟩
    · exact Or.inr (by simp [X, hh])
  have hle := (card_le_card hcover).trans (card_union_le _ _)
  have hdeg := hO X
  unfold touchCount at hfeas
  omega

omit [DecidableEq ι] in
/-- **Frank's orientation theorem, zero-potential form.** A `k`-weakly partition-connected
family of nonempty edges has, for every root `r`, an orientation with total root deficiency
`0`. -/
theorem exists_totalRootDeficiency_eq_zero {k : ℕ} (e : ι → Finset V)
    (hne : ∀ i, (e i).Nonempty) (hwpc : WeaklyPartitionConnected k (univ : Finset V) e)
    (r : V) : ∃ O : HeadOrientation e, totalRootDeficiency O r k = 0 := by
  classical
  have h0 : Feasible e r k 0 := by
    intro X
    simp only [Pi.zero_apply, sum_const_zero, zero_add]
    unfold req
    split_ifs with hX
    · have hXu : X ≠ univ := fun h => hX.2 (h ▸ mem_univ r)
      exact (wpc_border_ge e X hX.1 hXu hwpc).trans (card_le_card fun i hi => by
        simp only [mem_filter, mem_univ, true_and, borderEdges] at hi ⊢
        exact hi.1)
    · exact Nat.zero_le _
  obtain ⟨m, hm, hblock⟩ := exists_feasible_forall_mem_tight h0
  obtain ⟨O, hO⟩ := exists_orientation_inDegree_le hm (card_le_sum_of_blocked hne hwpc hm hblock)
  refine ⟨O, (totalRootDeficiency_eq_zero_iff O r k).2 fun T hT => ?_⟩
  obtain ⟨hrT, hTne⟩ := mem_properRootCuts.1 hT
  exact cutDeficiency_eq_zero_of_le O T (le_card_headBorderEdges hm O hO hrT hTne)

end FrankOrientation

variable (ι : Type*) [Fintype ι]

/-- **`FrankUncrossingResidual` is discharged.** Any positive-potential orientation is beaten
by the zero-potential orientation of `FrankOrientation.exists_totalRootDeficiency_eq_zero`. -/
theorem frankUncrossingResidual_holds (k : ℕ) : FrankUncrossingResidual ι k := by
  intro t _ e hne hwpc r O hpos
  obtain ⟨O', hO'⟩ := FrankOrientation.exists_totalRootDeficiency_eq_zero e hne hwpc r
  exact ⟨O', hO'.symm ▸ hpos⟩

/-- **Frank's rooted out-cut theorem** ([AGL24] Theorem A.3), unconditionally. -/
theorem frankRootedOutCutTheorem_holds (k : ℕ) : FrankRootedOutCutTheorem (ι := ι) k :=
  frankRootedOutCutTheorem_of_uncrossingResidual ι (frankUncrossingResidual_holds ι k)

/-- **`FrankOrientationResidual` is discharged**, through the existing descent and out-cut
glue. -/
theorem frankOrientationResidual_holds (k : ℕ) : FrankOrientationResidual ι k :=
  frankOrientationResidual_of_uncrossingResidual ι (frankUncrossingResidual_holds ι k)

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.FrankOrientation.exists_totalRootDeficiency_eq_zero
#print axioms AGL24.frankUncrossingResidual_holds
#print axioms AGL24.frankRootedOutCutTheorem_holds
#print axioms AGL24.frankOrientationResidual_holds
