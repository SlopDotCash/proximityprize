/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.AGL24GrandAssembly
import ArkLib.Data.CodingTheory.AGL24Submodular

/-!
# [AGL24]/Frank: standard rooted out-cut interface

Frank's hypergraph orientation theorem is usually stated as a rooted out-connectivity
statement: after choosing a root, every nonempty set avoiding the root has at least `k`
oriented hyperedges leaving it. The `FrankOrientationResidual` interface in
`AGL24GrandAssembly` is the complement form used by the generic-zero-pattern counting
argument: every proper root-containing set has at least `k` entering head-border edges.

This file proves the finite-set glue between those two formulations. It does not prove
Frank's theorem itself; it narrows the remaining import boundary to the standard
rooted out-cut statement from Frank's orientation theorem.
-/

open Finset

namespace AGL24

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- Edges oriented out of a vertex set `S`: the head is outside `S`, while the edge touches
`S`. In dypergraph terminology, these are the directed hyperedges leaving `S`. -/
noncomputable def rootedOutEdges {e : ι → Finset V} (O : HeadOrientation e)
    (S : Finset V) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => O.head i ∉ S ∧ (e i ∩ S).Nonempty)

omit [DecidableEq ι] [Fintype V] in
@[simp] theorem mem_rootedOutEdges {e : ι → Finset V}
    (O : HeadOrientation e) (S : Finset V) (i : ι) :
    i ∈ rootedOutEdges O S ↔ O.head i ∉ S ∧ (e i ∩ S).Nonempty := by
  classical
  simp [rootedOutEdges]

/-- Standard rooted out-cut condition: every nonempty set avoiding `r` has `k` outgoing
oriented hyperedges. This is the cut form of Frank's rooted weak-partition-connectivity
orientation theorem. -/
def RootedOutCutCondition {e : ι → Finset V} (O : HeadOrientation e) (r : V)
    (k : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → r ∉ S → k ≤ (rootedOutEdges O S).card

theorem nonempty_inter_univ_sdiff_of_not_subset {E T : Finset V}
    (h : ¬ E ⊆ T) : (E ∩ (Finset.univ \ T)).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply h
  intro x hxE
  by_contra hxT
  have hx : x ∈ E ∩ (Finset.univ \ T) := by
    exact Finset.mem_inter.mpr
      ⟨hxE, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxT⟩⟩
  rw [hempty] at hx
  exact Finset.notMem_empty x hx

theorem not_subset_of_nonempty_inter_univ_sdiff {E T : Finset V}
    (h : (E ∩ (Finset.univ \ T)).Nonempty) : ¬ E ⊆ T := by
  intro hsub
  obtain ⟨x, hx⟩ := h
  rw [Finset.mem_inter, Finset.mem_sdiff] at hx
  exact hx.2.2 (hsub hx.1)

omit [DecidableEq ι] in
/-- Complement translation: an edge leaves `univ \ T` exactly when its head-border enters
`T`. -/
theorem rootedOutEdges_univ_sdiff_eq_headBorderEdges {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) :
    rootedOutEdges O (Finset.univ \ T) = headBorderEdges O T := by
  classical
  ext i
  rw [mem_rootedOutEdges, mem_headBorderEdges]
  constructor
  · intro h
    refine ⟨?_, not_subset_of_nonempty_inter_univ_sdiff h.2⟩
    by_contra hhead
    exact h.1 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hhead⟩)
  · intro h
    refine ⟨?_, nonempty_inter_univ_sdiff_of_not_subset h.2⟩
    intro hhead
    exact (Finset.mem_sdiff.mp hhead).2 h.1

theorem univ_sdiff_nonempty_of_ne_univ {T : Finset V}
    (hTne : T ≠ Finset.univ) : (Finset.univ \ T).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply hTne
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    by_contra hxT
    have hx : x ∈ Finset.univ \ T :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxT⟩
    rw [hempty] at hx
    exact Finset.notMem_empty x hx

omit [DecidableEq ι] in
/-- The standard rooted out-cut condition gives the root-containing crossing supply used
by `gzp_of_orientation`. -/
theorem frank_cross_of_rootedOutCut {e : ι → Finset V} (O : HeadOrientation e)
    (r : V) {k : ℕ} (hout : RootedOutCutCondition O r k) :
    ∀ T : Finset V, r ∈ T → T ≠ Finset.univ →
      k ≤ (Finset.univ.filter (fun i => O.head i ∈ T ∧ ¬ e i ⊆ T)).card := by
  intro T hrT hTne
  have hS : (Finset.univ \ T).Nonempty := univ_sdiff_nonempty_of_ne_univ hTne
  have hrS : r ∉ Finset.univ \ T := by
    intro hr
    exact (Finset.mem_sdiff.mp hr).2 hrT
  have h := hout (Finset.univ \ T) hS hrS
  rw [rootedOutEdges_univ_sdiff_eq_headBorderEdges, headBorderEdges] at h
  exact h

omit [DecidableEq ι] in
/-- If the complement of the root is nonempty, the rooted out-cut condition also forces
the root's in-degree to be at least `k`. -/
theorem root_inDegree_ge_of_rootedOutCut {e : ι → Finset V} (O : HeadOrientation e)
    (r : V) {k : ℕ} (hcompl : (Finset.univ \ ({r} : Finset V)).Nonempty)
    (hout : RootedOutCutCondition O r k) :
    k ≤ O.inDegree r := by
  have h := hout (Finset.univ \ ({r} : Finset V)) hcompl (by simp)
  change k ≤ (Finset.univ.filter (fun i => O.head i = r)).card
  refine le_trans h (Finset.card_le_card ?_)
  intro i hi
  rw [mem_rootedOutEdges] at hi
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hne
  have hhead : O.head i ∈ Finset.univ \ ({r} : Finset V) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simpa using hne⟩
  exact hi.1 hhead

/-- Published-theorem-shaped import boundary for Frank's theorem: every WPC hypergraph
admits a rooted orientation satisfying the standard out-cut condition. -/
def FrankRootedOutCutTheorem (k : ℕ) : Prop :=
  ∀ {t : ℕ}, 1 ≤ t → ∀ e : ι → Finset (Fin (t + 1)),
    (∀ i, (e i).Nonempty) →
    WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
    ∃ O : HeadOrientation e, ∃ r : Fin (t + 1), RootedOutCutCondition O r k

omit [DecidableEq ι] in
/-- The standard rooted out-cut form of Frank's theorem implies ArkLib's existing
`FrankOrientationResidual` interface. -/
theorem frankOrientationResidual_of_rootedOutCutTheorem {k : ℕ}
    (hfrank : FrankRootedOutCutTheorem (ι := ι) k) :
    FrankOrientationResidual ι k := by
  intro t ht e hne hwpc
  obtain ⟨O, r, hout⟩ := hfrank ht e hne hwpc
  refine ⟨O, r, ?_, frank_cross_of_rootedOutCut O r hout⟩
  refine root_inDegree_ge_of_rootedOutCut O r ?_ hout
  rw [← Finset.card_pos]
  rw [Finset.card_sdiff]
  simp [Fintype.card_fin]
  omega

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.rootedOutEdges_univ_sdiff_eq_headBorderEdges
#print axioms AGL24.frankOrientationResidual_of_rootedOutCutTheorem
