/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Cardinality/finrank bricks for the CZ25 dimension count

Two mathlib-only counting facts that the CZ25 subspace-design dimension-count proximity work
(`ListDecoding/CZ25SpanDimension.lean`, `ToMathlib/CZ25DimensionCountProof.lean`, issues #93/#94)
currently proves inline:

* `LinearIndependent.card_le_finrank_of_mem_submodule` — an independent subfamily whose members
  lie in a finite-dimensional submodule `W` has cardinality at most `finrank W`. This is the
  reusable kernel of `finrank_inf_ker_ge_card_vanishing` (which restricts a basis to the indices
  vanishing at a coordinate, lands them in `A ⊓ ker (proj i)`, and reads off the dimension bound).
  Mathlib's `LinearIndependent.fintype_card_le_finrank` only bounds by `finrank` of the *whole*
  module; the submodule-relative version requires the subtype-restriction / lift-through-`W.subtype`
  dance done by hand at the use site.

* `Finset.card_add_card_sub_card_univ_le_card_inter` — the Bonferroni lower bound
  `|s| + |t| - |α| ≤ |s ∩ t|`, used in `card_diff_vanish_ge_of_mem_closeCodewordsRel` to show two
  large agreement sets intersect in `≥ (1 - 2δ)·n` coordinates. Mathlib has the *equality*
  `Finset.card_inter` but not this universe-relative lower bound.
-/

namespace LinearIndependent

/-- An independent subfamily `{b t : t ∈ S}` all of whose members lie in a finite-dimensional
submodule `W` has cardinality at most `Module.finrank R W`. Generalises the whole-module
`LinearIndependent.fintype_card_le_finrank` to a proper submodule. -/
theorem card_le_finrank_of_mem_submodule
    {R M : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]
    {κ : Type*} {b : κ → M} (hb : LinearIndependent R b)
    (W : Submodule R M) [Module.Finite R W] (S : Finset κ) (hS : ∀ t ∈ S, b t ∈ W) :
    S.card ≤ Module.finrank R W := by
  have hmem : ∀ t : {t // t ∈ S}, b t.1 ∈ W := by
    rintro ⟨t, ht⟩; exact hS t ht
  have hindep : LinearIndependent R (fun t : {t // t ∈ S} => (⟨b t.1, hmem t⟩ : W)) := by
    have hcomp := hb.comp (fun t : {t // t ∈ S} => t.1) Subtype.val_injective
    have hsub : LinearIndependent R
        (fun t : {t // t ∈ S} => (W.subtype) (⟨b t.1, hmem t⟩)) := by simpa using hcomp
    exact hsub.of_comp _
  have hcard := hindep.fintype_card_le_finrank
  rwa [Fintype.card_coe] at hcard

end LinearIndependent

namespace Finset

/-- Bonferroni lower bound on an intersection: `|s| + |t| - |α| ≤ |s ∩ t|`. The complement of the
mathlib equality `Finset.card_inter`, obtained by bounding `|s ∪ t| ≤ |α|`. -/
theorem card_add_card_sub_card_univ_le_card_inter
    {α : Type*} [Fintype α] [DecidableEq α] (s t : Finset α) :
    s.card + t.card - Fintype.card α ≤ (s ∩ t).card := by
  have h := Finset.card_union_add_card_inter s t
  have h2 := Finset.card_le_univ (s ∪ t)
  omega

end Finset

#print axioms LinearIndependent.card_le_finrank_of_mem_submodule
#print axioms Finset.card_add_card_sub_card_univ_le_card_inter
