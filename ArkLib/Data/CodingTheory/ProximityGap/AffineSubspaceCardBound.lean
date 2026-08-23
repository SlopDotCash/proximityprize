/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib


/-!
# Codewords in a low-dimensional affine subspace are few (B2 list-size cardinality) (#389, #334)

The cardinality half of the subspace-design list-size bound.  `card_le_pow_finrank_of_sub_mem`: if
every element of a finite set `L` lies in an affine subspace `c₀ + W`, then `|L| ≤ |F|^{dim W}`
(inject `c ↦ c − c₀` into `W`, whose underlying set has `|F|^{dim W}` elements).

Combined with `subspaceDesign_list_dim_bound` — which shows the list of codewords close to a word is
confined to a subspace of dimension `< r` — this yields the explicit list-size bound
`|list| ≤ |F|^{r−1}`, the curve-decodability list size from the subspace design.  Axiom-clean.
-/
open Finset

namespace ProximityGap

variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V] [Fintype V]

/-- **Codewords in a low-dimensional affine subspace are few.**  If every element of a finite set
`L` lies in the affine subspace `c₀ + W`, then `|L| ≤ |F|^{dim W}`.  This is the cardinality half of
the subspace-design list-size bound: combined with `subspaceDesign_list_dim_bound` (which confines
the list of close codewords to a subspace of dimension `< r`), it yields `|list| ≤ |F|^{r−1}`. -/
theorem card_le_pow_finrank_of_sub_mem (W : Submodule F V) (c₀ : V) (L : Finset V)
    (hL : ∀ c ∈ L, c - c₀ ∈ W) :
    L.card ≤ Fintype.card F ^ Module.finrank F W := by
  classical
  haveI : Fintype ↥W := Fintype.ofFinite _
  have hinj : Function.Injective (fun c : V => c - c₀) := sub_left_injective
  have h2 : L.image (fun c => c - c₀) ⊆ (W : Set V).toFinset := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    rw [Set.mem_toFinset]
    exact hL c hc
  calc L.card = (L.image (fun c => c - c₀)).card :=
        (Finset.card_image_of_injective L hinj).symm
    _ ≤ (W : Set V).toFinset.card := Finset.card_le_card h2
    _ = Fintype.card F ^ Module.finrank F W := by
        rw [Set.toFinset_card]; exact Module.card_eq_pow_finrank

end ProximityGap
