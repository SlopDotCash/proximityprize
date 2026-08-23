/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Complement symmetry of subset sumsets (issue #232)

When the total sum over a finite set `G` vanishes — e.g. `G` a nontrivial finite subgroup of a
field's units (`sum_subgroup_units_eq_zero`), in particular any 2-power multiplicative subgroup
of a smooth domain — complementation `S ↦ G \ S` negates subset sums. Hence the `(|G|−ℓ)`-subset
sumset is the negation of the `ℓ`-subset sumset, and they have equal cardinality.

This makes the bad-scalar counts of the KK-type smooth-domain constructions uniform across the
four prize rates (the §7-critical layer `ℓ = (1−ρ)|E|−2` mirrors to a low layer; DISPROOF_LOG
O11′/O11‴): the `e₁`-image sizes `N₀(m, r)` and `N₀(m, m−r)` coincide.
-/

open Finset

namespace ArkLib.SmoothDomain

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

/-- If the total sum over `G` vanishes, complementation negates subset sums. -/
theorem sum_sdiff_eq_neg_of_sum_eq_zero {G S : Finset F} (hG : ∑ g ∈ G, g = 0)
    (hS : S ⊆ G) : ∑ g ∈ G \ S, g = -∑ g ∈ S, g := by
  have h := Finset.sum_sdiff (f := fun g : F => g) hS
  have h0 : ∑ g ∈ G \ S, g + ∑ g ∈ S, g = 0 := by rw [h, hG]
  exact eq_neg_of_add_eq_zero_left h0

/-- **Complement symmetry of subset sumsets.** When the total sum over `G` vanishes, the
`(|G|−ℓ)`-subset sumset is the negation of the `ℓ`-subset sumset. -/
theorem subset_sumset_compl_image_eq
    (G : Finset F) (hG : ∑ g ∈ G, g = 0) (ℓ : ℕ) (hℓ : ℓ ≤ G.card) :
    (G.powersetCard (G.card - ℓ)).image (fun S => ∑ g ∈ S, g)
      = ((G.powersetCard ℓ).image (fun S => ∑ g ∈ S, g)).image (fun x => -x) := by
  classical
  ext x
  simp only [mem_image, mem_powersetCard]
  constructor
  · rintro ⟨T, ⟨hT, hTcard⟩, rfl⟩
    refine ⟨∑ g ∈ G \ T, g, ⟨G \ T, ⟨sdiff_subset, ?_⟩, rfl⟩, ?_⟩
    · rw [card_sdiff, inter_eq_left.mpr hT, hTcard]; omega
    · rw [sum_sdiff_eq_neg_of_sum_eq_zero hG hT, neg_neg]
  · rintro ⟨y, ⟨S, ⟨hS, hScard⟩, rfl⟩, rfl⟩
    refine ⟨G \ S, ⟨sdiff_subset, by rw [card_sdiff, inter_eq_left.mpr hS, hScard]⟩, ?_⟩
    exact sum_sdiff_eq_neg_of_sum_eq_zero hG hS

/-- Cardinality form: the `ℓ`- and `(|G|−ℓ)`-subset sumsets have equal size. -/
theorem subset_sumset_compl_card_eq
    (G : Finset F) (hG : ∑ g ∈ G, g = 0) (ℓ : ℕ) (hℓ : ℓ ≤ G.card) :
    ((G.powersetCard (G.card - ℓ)).image (fun S => ∑ g ∈ S, g)).card
      = ((G.powersetCard ℓ).image (fun S => ∑ g ∈ S, g)).card := by
  rw [subset_sumset_compl_image_eq G hG ℓ hℓ]
  exact card_image_of_injective _ neg_injective


end ArkLib.SmoothDomain

#print axioms ArkLib.SmoothDomain.subset_sumset_compl_image_eq
#print axioms ArkLib.SmoothDomain.subset_sumset_compl_card_eq
