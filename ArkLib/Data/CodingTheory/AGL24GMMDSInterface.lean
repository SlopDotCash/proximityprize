/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.AGL24GrandAssembly

/-!
# [AGL24]/GM-MDS: copied-row interface

The existing `GMMDSResidual` is already the object consumed by the Appendix A assembly:
dual vectors, each supported on the edge set of one vertex, spanning the Reed-Solomon
dual. This file narrows that residual to the row-indexed shape used by AGL24 Theorem A.2
and Corollary A.4.

Given a multiplicity function `delta`, the GM-MDS rows are indexed by copies of vertices:
one row for each element of `GZPCopyIdx delta`. The theorem below says that every GZP
has such copied rows. The final wrapper forgets this structured index by enumerating the
finite copy type with `Fin d`, yielding the older `GMMDSResidual` interface.

This file does not prove the GM-MDS theorem itself. It records the faithful imported
boundary in the form nearest to the paper and proves the in-tree plumbing from that
boundary to the residual consumed by `symbolicFullRank_of_classical_imports`.
-/

open Finset

namespace AGL24

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]
variable {F : Type*} [Field F]

/-- The copied row index for a generic zero pattern with vertex multiplicities `delta`.
An element is a vertex together with one of its `delta` copies. -/
abbrev GZPCopyIdx (delta : V -> Nat) : Type _ :=
  Sigma fun j : V => Fin (delta j)

/-- The vertex underlying a copied GZP row. -/
def GZPCopyIdx.vertex {delta : V -> Nat} (a : GZPCopyIdx delta) : V :=
  a.1

/-- Structured, paper-shaped GM-MDS import boundary: for every GZP, there are evaluation
points and one dual row per copied vertex, each supported on the coordinates whose edge
contains that vertex, and these rows span the Reed-Solomon dual. -/
def GMMDSDualZeroPatternTheorem (k : Nat) : Prop :=
  forall {t : Nat}, forall e : ι -> Finset (Fin (t + 1)), forall delta : Fin (t + 1) -> Nat,
    GZPCondition e delta k ->
    exists phi : ι ↪ F, exists h : GZPCopyIdx delta -> (ι -> F),
      (forall a : GZPCopyIdx delta, forall i : ι, a.vertex ∉ e i -> h a i = 0) /\
      Submodule.span F (Set.range h) =
        dotForm.orthogonal (ReedSolomon.code phi k)

omit [DecidableEq ι] in
/-- Reindex a finite family by `Fin (Fintype.card alpha)` without changing its span. -/
theorem span_range_reindex_equivFin {alpha M : Type*} [Fintype alpha]
    [AddCommMonoid M] [Module F M] (h : alpha -> M) :
    Submodule.span F (Set.range (fun i : Fin (Fintype.card alpha) =>
        h ((Fintype.equivFin alpha).symm i))) =
      Submodule.span F (Set.range h) := by
  classical
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(Fintype.equivFin alpha).symm i, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(Fintype.equivFin alpha) a, ?_⟩
    simp

omit [DecidableEq ι] in
/-- The copied-row GM-MDS theorem implies ArkLib's older existential `GMMDSResidual`
interface by forgetting the structured copy index. -/
theorem gmmDsResidual_of_dualZeroPatternTheorem {k : Nat}
    (hgm : GMMDSDualZeroPatternTheorem (ι := ι) (F := F) k) :
    GMMDSResidual ι F k := by
  classical
  intro t e delta hgzp
  obtain ⟨phi, h, hsupp, hspan⟩ := hgm e delta hgzp
  refine ⟨phi, Fintype.card (GZPCopyIdx delta),
    fun a => h ((Fintype.equivFin (GZPCopyIdx delta)).symm a), ?_, ?_⟩
  · intro a
    refine ⟨((Fintype.equivFin (GZPCopyIdx delta)).symm a).vertex, ?_⟩
    intro i hi
    exact hsupp ((Fintype.equivFin (GZPCopyIdx delta)).symm a) i hi
  · rw [span_range_reindex_equivFin]
    exact hspan

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.span_range_reindex_equivFin
#print axioms AGL24.gmmDsResidual_of_dualZeroPatternTheorem
