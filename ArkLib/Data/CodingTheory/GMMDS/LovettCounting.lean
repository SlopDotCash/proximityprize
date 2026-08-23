/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Lovett's GM-MDS proof: the basis-counting transfer (#389)

Lovett's Lemma 2.4 (arXiv:1803.02523) concludes `P(k,V)` independent from: `P(k,V')` independent,
`P(k,V)` and `P(k,V')` span the **same space**, and `|P(k,V)| = |P(k,V')|`.  This is the classic
field argument "a spanning set of size = dimension is a basis, hence independent".

This file isolates that kernel over a field: two finite families with the same index type and the
same span, one independent ⟹ the other independent.  (Over the fraction field `F(a)`, reached via
[[LovettFractionField]].)

Issue #389.
-/

open Submodule

namespace ArkLib.GMMDS

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- **Basis-counting transfer.**  Two finite families over a field with the same span: if one is
linearly independent, so is the other (equal cardinality is automatic — same index type). -/
theorem linearIndependent_of_span_eq {g g' : ι → V}
    (hspan : Submodule.span K (Set.range g) = Submodule.span K (Set.range g'))
    (hg' : LinearIndependent K g') : LinearIndependent K g := by
  rw [linearIndependent_iff_card_le_finrank_span]
  have h' : Fintype.card ι = (Set.range g').finrank K :=
    linearIndependent_iff_card_eq_finrank_span.mp hg'
  have hfr : (Set.range g).finrank K = (Set.range g').finrank K := by
    unfold Set.finrank
    rw [hspan]
  rw [hfr]
  exact h'.le

/-- **Basis-counting transfer, distinct index types.**  If `g' : ι' → V` is independent, `g`
and `g'` have the **same span**, and their index types have **equal cardinality**, then `g` is
independent.  (The dimension of the common span equals `|ι'|` by independence of `g'`, hence
equals `|ι|`, which forces `g` independent.) -/
theorem linearIndependent_of_span_eq_card {ι' : Type*} [Fintype ι']
    {g : ι → V} {g' : ι' → V}
    (hspan : Submodule.span K (Set.range g) = Submodule.span K (Set.range g'))
    (hcard : Fintype.card ι = Fintype.card ι')
    (hg' : LinearIndependent K g') : LinearIndependent K g := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  have h' : Fintype.card ι' = (Set.range g').finrank K :=
    linearIndependent_iff_card_eq_finrank_span.mp hg'
  have hfr : (Set.range g).finrank K = (Set.range g').finrank K := by
    unfold Set.finrank; rw [hspan]
  rw [hfr, ← h', hcard]

/-- **Reverse-direction span equality (the dimension-counting core of Lemma 2.4).**  Over a field,
if `g` and `g'` are both linearly independent finite families with `span g ≤ span g'` and equal
index cardinality, then their spans are **equal**.  (Both spans are finite-dimensional of the same
dimension `|ι| = |ι'|`, and one is contained in the other.)

This is the half of the equal-span transfer that the forward inclusion alone cannot give: it
requires `g` (the `I`-block) to *also* be independent — the genuine extra input of Lovett's Lemma
2.4, supplied in the proof by the independence of the `I`-subsystem. -/
theorem span_eq_of_le_of_card_of_indep {ι' : Type*} [Fintype ι']
    {g : ι → V} {g' : ι' → V}
    (hle : Submodule.span K (Set.range g) ≤ Submodule.span K (Set.range g'))
    (hcard : Fintype.card ι = Fintype.card ι')
    (hg : LinearIndependent K g) (hg' : LinearIndependent K g') :
    Submodule.span K (Set.range g) = Submodule.span K (Set.range g') := by
  classical
  haveI : FiniteDimensional K (Submodule.span K (Set.range g')) :=
    FiniteDimensional.span_of_finite K (Set.finite_range g')
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  -- goal: finrank (span g') ≤ finrank (span g)
  have hg_fr : Module.finrank K (Submodule.span K (Set.range g)) = Fintype.card ι :=
    finrank_span_eq_card hg
  have hg'_fr : Module.finrank K (Submodule.span K (Set.range g')) = Fintype.card ι' :=
    finrank_span_eq_card hg'
  rw [hg_fr, hg'_fr, hcard]

end ArkLib.GMMDS

#print axioms ArkLib.GMMDS.linearIndependent_of_span_eq
#print axioms ArkLib.GMMDS.linearIndependent_of_span_eq_card
#print axioms ArkLib.GMMDS.span_eq_of_le_of_card_of_indep
