/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G136LawfulCount
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg

/-!
# G139: Sidon-modulo-negation excludes normalized accidents

This follow-up isolates the clean formal bridge consumed by the
`Phi_H` certificate story:

```text
SidonModNeg H  ==>  #accidents(H) = 0.
```

The proof is purely structural.  If `((a,b),c)` is a normalized solution
`a + b = c + 1`, then applying `SidonModNeg` to the equality
`a + b = c + 1` leaves only the three Mann families:

* `a = c`, `b = 1`;
* `a = 1`, `b = c`;
* `a + b = 0`, hence `b = -a` and `c = -1`.

So every solution is lawful, and the accident set is empty.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G139SidonModNegClean

open Finset
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg
open ArkLib.ProximityGap.Frontier.G136EnergySolutionBijection
open ArkLib.ProximityGap.Frontier.G136LawfulCount

variable {F : Type*} [Field F] [DecidableEq F]

/-- `SidonModNeg` leaves only the three lawful Mann families among normalized
G139 rung-2 solutions. -/
theorem solutions_subset_lawful_of_sidonModNeg
    {H : Finset F} (h1 : (1 : F) ∈ H) (hS : SidonModNeg H) :
    solutions H ⊆ lawful H := by
  intro p hp
  unfold solutions at hp
  rw [Finset.mem_filter] at hp
  rcases p with ⟨⟨a, b⟩, c⟩
  rcases hp with ⟨hpH, hsol⟩
  rw [Finset.mem_product] at hpH
  rcases hpH with ⟨habH, hc⟩
  rw [Finset.mem_product] at habH
  rcases habH with ⟨ha, hb⟩
  have hsol' : a + b = c + 1 := by simpa using hsol
  have hsid := hS a ha b hb c hc 1 h1 hsol'
  unfold lawful
  rw [Finset.mem_union, Finset.mem_union]
  rcases hsid with hsame | hswap | hzero
  · rcases hsame with ⟨hac, hb1⟩
    left
    right
    exact Finset.mem_image.mpr ⟨a, ha, by simp [hac, hb1]⟩
  · rcases hswap with ⟨ha1, hbc⟩
    left
    left
    exact Finset.mem_image.mpr ⟨b, hb, by simp [ha1, hbc]⟩
  · right
    have hbneg : b = -a := by linear_combination hzero
    have hcplus : c + 1 = 0 := by
      rw [← hsol']
      exact hzero
    have hcneg : c = -1 := by linear_combination hcplus
    exact Finset.mem_image.mpr ⟨a, ha, by simp [hbneg, hcneg]⟩

/-- A Sidon-modulo-negation subgroup has no non-lawful normalized G139 accidents. -/
theorem accidents_eq_empty_of_sidonModNeg
    {H : Finset F} (h1 : (1 : F) ∈ H) (hS : SidonModNeg H) :
    accidents H = ∅ := by
  unfold accidents
  exact Finset.sdiff_eq_empty_iff_subset.mpr
    (solutions_subset_lawful_of_sidonModNeg h1 hS)

/-- Cardinality form of `accidents_eq_empty_of_sidonModNeg`. -/
theorem accidents_card_eq_zero_of_sidonModNeg
    {H : Finset F} (h1 : (1 : F) ∈ H) (hS : SidonModNeg H) :
    (accidents H).card = 0 := by
  rw [accidents_eq_empty_of_sidonModNeg h1 hS]
  simp

end ArkLib.ProximityGap.Frontier.G139SidonModNegClean

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G139SidonModNegClean.accidents_card_eq_zero_of_sidonModNeg
