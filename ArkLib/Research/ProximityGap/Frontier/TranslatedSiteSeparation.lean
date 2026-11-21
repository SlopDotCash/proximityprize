/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! # Removing collisions of translated evaluation sites

A common locator can absorb every first endpoint of a collision. Averaging
over nonzero dilations bounds the required locator degree on every domain.
-/
set_option autoImplicit false

namespace ProximityGap.TranslatedSiteSeparation
open Finset

/-- After excluding exactly h sites, all translates of the remaining sites by
one common nonzero dilation of V are pairwise distinct as site-value pairs. -/
theorem exists_separated {I F : Type*} [Fintype I] [DecidableEq I] [Field F]
    [Fintype F] [DecidableEq F] (x : I ↪ F) (V : Finset F) (h : ℕ)
    (available : h ≤ Fintype.card I)
    (room : (univ : Finset I).offDiag.card * V.offDiag.card ≤ (Fintype.card F-1)*h) :
    ∃ t : F, t≠0 ∧ ∃ S : Finset I, S.card=h ∧
      ∀ ⦃i j : I⦄, i∉S → j∉S → ∀ ⦃v w : F⦄, v∈V → w∈V →
        x i+t*v=x j+t*w → i=j ∧ v=w := by
  classical
  let pairs := (univ : Finset I).offDiag ×ˢ V.offDiag
  let ratio (z : (I×I)×(F×F)) := (x z.1.1 - x z.1.2)/(z.2.2-z.2.1)
  let units := (univ : Finset F).erase 0
  have hn : units.Nonempty := ⟨1,mem_erase.mpr ⟨one_ne_zero,mem_univ _⟩⟩
  have budget : pairs.card≤units.card*h := by simpa [pairs,units,card_erase_of_mem] using room
  obtain ⟨t, ht, hf⟩ := exists_card_fiber_le_of_card_le_mul (f:=ratio) hn budget
  let collisions := pairs.filter (fun z => ratio z=t)
  let sites := collisions.image (fun z => z.1.1)
  have bound : sites.card ≤ h := card_image_le.trans hf
  obtain ⟨S,inS,cardS⟩ := exists_superset_card_eq bound available
  have nz := (mem_erase.mp ht).1
  refine ⟨t,nz,S,cardS,?_⟩
  intro i j hi _ v w hv hw eq
  by_cases same : i=j
  · subst j
    exact ⟨rfl,mul_left_cancel₀ nz (add_left_cancel eq)⟩
  have diff : v≠w := by
    rintro rfl
    exact same (x.injective (add_right_cancel eq))
  have coll : ((i,j),(v,w)) ∈ collisions := by
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_offDiag.mpr ⟨mem_univ _,mem_univ _,same⟩,
      mem_offDiag.mpr ⟨hv,hw,diff⟩⟩, ?_⟩
    apply (div_eq_iff (sub_ne_zero.mpr diff.symm)).mpr
    linear_combination eq
  exact False.elim (hi (inS (mem_image.mpr ⟨_,coll,rfl⟩)))

end ProximityGap.TranslatedSiteSeparation
#print axioms ProximityGap.TranslatedSiteSeparation.exists_separated
