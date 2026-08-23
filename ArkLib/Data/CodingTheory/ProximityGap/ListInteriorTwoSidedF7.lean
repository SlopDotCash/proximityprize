/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorDataPointF7
import ArkLib.Data.CodingTheory.ProximityGap.UniqueDecodingListBound
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A verified TWO-SIDED interior list-size pin for `RS[F₇, F₇, 2]` via Fisher pair-packing

`ListInteriorDataPointF7.lean` pins the interior list size of the explicit tiny code
`RS[F = ZMod 7, L = F₇, k = 2]` at the strictly-interior radius `δ = 4/7` **from below** (an explicit
`6`-element list, `interior_list_lower_bound`). This file supplies the **matching upper bound**, by a
fully-combinatorial *Fisher / Corrádi pair-packing* argument, turning that one-sided data point into a
verified, near-tight **two-sided pin `list ∈ [6, 7]`** — the first such two-sided interior data point
in the repo.

## The combinatorial core (`pairPacking_card_le`)

This is a self-contained, *code-free* lemma. Let `L` be a finite index set and `S : α → Finset ι` a
family of subsets of an `n`-element ground set such that

* each `S c` has `≥ a` elements, and
* any two **distinct** indices have `|S c ∩ S c'| ≤ 1` (pairwise meet in at most one point).

Then `|L| · C(a, 2) ≤ C(n, 2)`.

*Proof (double counting unordered pairs).* Send each `c` to its `2`-element subsets
`T c = (S c).powersetCard 2`, a subfamily of `(univ).powersetCard 2` (the `C(n,2)` pairs of the ground
set). Then `|T c| = C(|S c|, 2) ≥ C(a, 2)`. Two distinct `c, c'` cannot share a `2`-subset `{i,j}`: it
would lie in `S c ∩ S c'`, forcing `|S c ∩ S c'| ≥ 2 > 1`. So the `T c` are pairwise disjoint, hence
`|L| · C(a,2) ≤ ∑_c |T c| = |⋃_c T c| ≤ C(n, 2)`.

## The Reed–Solomon bridge (`reedSolomon_pairPacking_list_bound`)

For RS codewords of degree-`< k` polynomials, distinct codewords agree on `≤ k − 1` coordinates
(`agreement_card_le`). Take `S c = {i : c i = w i}` (the `w`-agreement set). Then `|S c| = agree c w`,
and for distinct codewords `|S c ∩ S c'| ≤ k − 1` because a common `w`-agreement coordinate forces the
two codewords to agree there. With `k = 2` the meet bound is `≤ 1`, so `pairPacking_card_le` applies:
a list of distinct degree-`< 2` RS codewords each agreeing with `w` on `≥ a` coordinates has
`|L| · C(a, 2) ≤ C(n, 2)`.

## The two-sided F₇ pin (`interior_list_upper_bound_seven`, `interior_list_two_sided`)

Instantiating at `RS[F₇, F₇, 2]`, `a = 3`, `n = 7`: `C(3,2) = 3`, `C(7,2) = 21`, so `3·|L| ≤ 21`,
i.e. `|L| ≤ 7`. Combined with the existing `6`-element witness, the true interior list size at the
strictly-interior radius `δ = 4/7` is provably in `[6, 7]`.

Everything is `sorry`-free and axiom-clean. The hypotheses are satisfiable: the lower-bound witness is
the explicit list `L` from `ListInteriorDataPointF7.lean`, so the `[6, 7]` window is non-empty and the
upper bound is genuinely *attained-within-one*. This is a verified near-tight interior list-size data
point — not a general matching upper bound for smooth-domain RS (the open prize), but the sharpest
two-sided pin one can extract from a single explicit instance by elementary pair-packing.
-/

namespace ArkLib.CodingTheory.TinyInteriorTwoSided

open Finset
open ArkLib.CodingTheory.UniqueDecoding ArkLib.CodingTheory.JohnsonSimplex

/-! ## The abstract Fisher / Corrádi pair-packing lemma -/

variable {α : Type*} {ι : Type*} [DecidableEq ι]

/-- **Fisher / Corrádi pair-packing.** Let `L : Finset α` index a family `S : α → Finset ι` of subsets
of a ground set `ground : Finset ι`, where each `S c ⊆ ground` has `≥ a` elements and any two distinct
indices satisfy `|S c ∩ S c'| ≤ 1`. Then `|L| · C(a, 2) ≤ C(|ground|, 2)`.

Proof: each `c` contributes its `C(|S c|, 2) ≥ C(a, 2)` two-element subsets, which all live among the
`C(|ground|, 2)` two-element subsets of `ground`; distinct indices share no two-element subset (that
would force their intersection to have `≥ 2` elements), so the contributions are disjoint and sum to
at most `C(|ground|, 2)`. -/
theorem pairPacking_card_le {ground : Finset ι} {S : α → Finset ι} {L : Finset α} {a : ℕ}
    (hsub : ∀ c ∈ L, S c ⊆ ground)
    (hge : ∀ c ∈ L, a ≤ (S c).card)
    (hmeet : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → ((S c) ∩ (S c')).card ≤ 1) :
    L.card * a.choose 2 ≤ ground.card.choose 2 := by
  classical
  -- `T c` = the 2-element subsets of `S c`, viewed inside the 2-element subsets of `ground`.
  set T : α → Finset (Finset ι) := fun c => (S c).powersetCard 2 with hT
  -- Each `T c` is a subfamily of `powersetCard 2 ground`.
  have hTsub : ∀ c ∈ L, T c ⊆ ground.powersetCard 2 := fun c hc =>
    powersetCard_mono (hsub c hc)
  -- Pairwise disjointness of the `T c`.
  have hdisj : (↑L : Set α).PairwiseDisjoint T := by
    intro c hc c' hc' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro u huc huc'
    -- `u` is a 2-subset of both `S c` and `S c'`, hence `u ⊆ S c ∩ S c'`.
    rw [hT, mem_powersetCard] at huc huc'
    have hu2 : u.card = 2 := huc.2
    have husub : u ⊆ (S c) ∩ (S c') := Finset.subset_inter huc.1 huc'.1
    have : (2 : ℕ) ≤ ((S c) ∩ (S c')).card := hu2 ▸ Finset.card_le_card husub
    have := hmeet c (Finset.mem_coe.mp hc) c' (Finset.mem_coe.mp hc') hne
    omega
  -- `|T c| = C(|S c|, 2) ≥ C(a, 2)`.
  have hTcard : ∀ c ∈ L, a.choose 2 ≤ (T c).card := by
    intro c hc
    rw [hT, card_powersetCard]
    exact Nat.choose_le_choose 2 (hge c hc)
  -- Double count: `Σ |T c| = |⋃ T c| ≤ C(|ground|, 2)`.
  calc L.card * a.choose 2
      = ∑ _c ∈ L, a.choose 2 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ c ∈ L, (T c).card := Finset.sum_le_sum hTcard
    _ = (L.biUnion T).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (ground.powersetCard 2).card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr hTsub)
    _ = ground.card.choose 2 := card_powersetCard 2 ground

/-! ## The Reed–Solomon bridge -/

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]

/-- **Reed–Solomon pair-packing list bound.** A list `L` of *distinct* words, each the evaluation
`i ↦ p(D i)` of some degree-`< 2` polynomial on an injective domain `D`, each agreeing with a
received word `w` on `≥ a` coordinates, satisfies `|L| · C(a, 2) ≤ C(n, 2)` where `n = |ι|`.

For `k = 2`, distinct degree-`< 2` codewords agree on `≤ k − 1 = 1` coordinate, so their
`w`-agreement sets meet in `≤ 1` point; apply `pairPacking_card_le` to `S c = {i : c i = w i}`. -/
theorem reedSolomon_pairPacking_list_bound (D : ι ↪ F) (w : ι → F)
    (L : Finset (ι → F)) (a : ℕ)
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < 2 ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, a ≤ agree c w) :
    L.card * a.choose 2 ≤ (Fintype.card ι).choose 2 := by
  classical
  -- The `w`-agreement set of a word.
  set S : (ι → F) → Finset ι := fun c => Finset.univ.filter (fun i => c i = w i) with hS
  have hground : (Finset.univ : Finset ι).card = Fintype.card ι := Finset.card_univ
  rw [← hground]
  refine pairPacking_card_le (ground := Finset.univ) (S := S) (L := L) (a := a)
    (fun c _ => Finset.subset_univ _) ?_ ?_
  · -- `|S c| = agree c w ≥ a`.
    intro c hc
    have : (S c).card = agree c w := rfl
    rw [this]; exact hclose c hc
  · -- distinct codewords: `|S c ∩ S c'| ≤ 1`.
    intro c hc c' hc' hne
    obtain ⟨p, hp, rfl⟩ := hpoly c hc
    obtain ⟨q, hq, rfl⟩ := hpoly c' hc'
    have hpq : p ≠ q := fun h => hne (by rw [h])
    -- A common `w`-agreement coordinate is a `p = q` coordinate.
    have hsubset : (S (fun i => p.eval (D i))) ∩ (S (fun i => q.eval (D i)))
        ⊆ Finset.univ.filter (fun i => p.eval (D i) = q.eval (D i)) := by
      intro i hi
      rw [hS, Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, hi.1.2.trans hi.2.2.symm⟩
    have hle : (Finset.univ.filter (fun i => p.eval (D i) = q.eval (D i))).card ≤ 2 - 1 :=
      agreement_card_le hp hq hpq
    calc ((S (fun i => p.eval (D i))) ∩ (S (fun i => q.eval (D i)))).card
        ≤ (Finset.univ.filter (fun i => p.eval (D i) = q.eval (D i))).card :=
          Finset.card_le_card hsubset
      _ ≤ 1 := by simpa using hle

/-! ## The two-sided F₇ interior pin -/

open ArkLib.CodingTheory.TinyInteriorPin

/-- **Interior list-size UPPER bound for `RS[F₇, F₇, 2]`.** Any list `L` of distinct degree-`< 2` RS
codewords on the smooth domain `D`, each agreeing with a received word `w` on `≥ 3` of the `7`
coordinates (i.e. within relative radius `δ = 4/7`, strictly inside the open gap), has `|L| ≤ 7`.

Proof: `pairPacking` gives `|L| · C(3, 2) ≤ C(7, 2)`, i.e. `3·|L| ≤ 21`, so `|L| ≤ 7`. -/
theorem interior_list_upper_bound_seven (w' : Fin 7 → ZMod 7)
    (L' : Finset (Fin 7 → ZMod 7))
    (hpoly : ∀ c ∈ L', ∃ q : (ZMod 7)[X], q.natDegree < 2 ∧ c = fun i => q.eval (D i))
    (hclose : ∀ c ∈ L', 3 ≤ agree c w') :
    L'.card ≤ 7 := by
  have h := reedSolomon_pairPacking_list_bound (ι := Fin 7) (F := ZMod 7) D w' L' 3 hpoly hclose
  -- `C(3,2) = 3`, `Fintype.card (Fin 7) = 7`, `C(7,2) = 21`.
  have e1 : (3 : ℕ).choose 2 = 3 := by decide
  have e2 : (7 : ℕ).choose 2 = 21 := by decide
  rw [Fintype.card_fin, e1, e2] at h
  -- now `h : L'.card * 3 ≤ 21`.
  omega

/-- **Two-sided interior list-size pin for `RS[F₇, F₇, 2]` at `δ = 4/7`.**

There exists a received word `w` and a list `L` of distinct degree-`< 2` Reed–Solomon codewords on
the smooth domain `D`, each agreeing with `w` on `≥ 3` of the `7` coordinates (relative radius
`δ = 4/7`, strictly interior to the open proximity gap `(1 − √(2/7), 5/7)` by
`four_sevenths_strictly_interior`), with **`6 ≤ |L|`**; and **every** such list has **`|L| ≤ 7`**.

So at this interior radius the list size of this explicit code is pinned to `[6, 7]` — a verified,
near-tight (within one) two-sided interior data point. The lower bound is the explicit witness of
`interior_list_lower_bound`; the upper bound is the Fisher pair-packing bound
`interior_list_upper_bound_seven`. This is the honest two-sided content of pinning `δ*` for a tiny
explicit instance: not the general matching upper bound the open prize lacks, but the sharpest
two-sided window elementary pair-packing yields here. -/
theorem interior_list_two_sided :
    (∃ (w' : Fin 7 → ZMod 7) (L' : Finset (Fin 7 → ZMod 7)),
        6 ≤ L'.card ∧
        (∀ c ∈ L', ∃ q : (ZMod 7)[X], q.natDegree < 2 ∧ c = fun i => q.eval (D i)) ∧
        (∀ c ∈ L', 3 ≤ agree c w')) ∧
    (∀ (w' : Fin 7 → ZMod 7) (L' : Finset (Fin 7 → ZMod 7)),
        (∀ c ∈ L', ∃ q : (ZMod 7)[X], q.natDegree < 2 ∧ c = fun i => q.eval (D i)) →
        (∀ c ∈ L', 3 ≤ agree c w') →
        L'.card ≤ 7) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨w', L', hcard, hpoly, hclose⟩ := interior_list_lower_bound
    exact ⟨w', L', by rw [hcard], hpoly, hclose⟩
  · exact fun w' L' hpoly hclose => interior_list_upper_bound_seven w' L' hpoly hclose

end ArkLib.CodingTheory.TinyInteriorTwoSided

#print axioms ArkLib.CodingTheory.TinyInteriorTwoSided.interior_list_two_sided
#print axioms ArkLib.CodingTheory.TinyInteriorTwoSided.pairPacking_card_le
