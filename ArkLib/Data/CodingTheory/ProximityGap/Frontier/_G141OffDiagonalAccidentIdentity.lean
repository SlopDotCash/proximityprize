/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G140QuantitativeAccidentDCFloor

/-!
# G141: `fiberEnergy - diagonal` is exactly the off-diagonal accident census

G140 proves the numerical DC floor for `fiberEnergy f - #X`.  This file identifies that
subtraction with a literal finite set: ordered distinct pairs having the same image under `f`.
Consequently the quantitative accident theorem becomes

`#X (#X - #Y) ≤ #Y · #offDiagonalCollisions(f)`.

For a subset-sum map these are precisely the modular collisions not explained by equality of the
two subsets.  Future cancellation-depth decompositions can therefore stratify an actual census,
not an opaque natural-number difference.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G141OffDiagonalAccidentIdentity

open ArkLib.ProximityGap.Frontier.G140QuantitativeAccidentDCFloor

/-- Ordered collision pairs of a finite map. -/
def collisionPairs {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) : Finset (X × X) :=
  Finset.univ.filter fun p => f p.1 = f p.2

/-- Ordered, genuinely distinct collision pairs: the literal accident census. -/
def offDiagonalCollisions {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) : Finset (X × X) :=
  Finset.univ.filter fun p => f p.1 = f p.2 ∧ p.1 ≠ p.2

/-- Fiber energy counts ordered collision pairs. -/
theorem fiberEnergy_eq_card_collisionPairs
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) :
    fiberEnergy f = (collisionPairs f).card := by
  classical
  unfold fiberEnergy collisionPairs fiberCount
  have hfc : ∀ y, Fintype.card {x : X // f x = y} =
      (Finset.univ.filter fun x => f x = y).card := by
    intro y
    rw [Fintype.card_subtype]
  simp_rw [hfc]
  calc
    ∑ y, ((Finset.univ.filter fun x : X => f x = y).card) ^ 2 =
        ∑ y, ((Finset.univ.filter fun x : X => f x = y) ×ˢ
          (Finset.univ.filter fun x : X => f x = y)).card := by
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.card_product, pow_two]
    _ = ∑ y, (Finset.univ.filter fun p : X × X =>
          f p.1 = y ∧ f p.2 = y).card := by
            apply Finset.sum_congr rfl
            intro y _
            congr 1
            ext p
            simp [Finset.mem_product]
    _ = (Finset.univ.filter fun p : X × X => f p.1 = f p.2).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext p
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
        constructor
        · rintro ⟨y, h1, h2⟩
          exact h1.trans h2.symm
        · intro h
          exact ⟨f p.1, rfl, h.symm⟩
      · intro a _ b _ hab
        apply Finset.disjoint_left.mpr
        intro p hp hq
        simp only [Finset.mem_filter] at hp hq
        exact hab (hp.2.1.symm.trans hq.2.1)

/-- Collision pairs split exactly into the diagonal and the off-diagonal accidents. -/
theorem card_collisionPairs_eq_card_add_offDiagonal
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) :
    (collisionPairs f).card = Fintype.card X + (offDiagonalCollisions f).card := by
  classical
  let diagonal : Finset (X × X) := Finset.univ.image fun x : X => (x, x)
  have hsplit : collisionPairs f = diagonal ∪ offDiagonalCollisions f := by
    ext p
    simp only [collisionPairs, offDiagonalCollisions, diagonal, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
    constructor
    · intro h
      by_cases heq : p.1 = p.2
      · left
        exact ⟨p.1, Prod.ext rfl heq⟩
      · exact Or.inr ⟨h, heq⟩
    · rintro (⟨x, -, rfl⟩ | ⟨h, -⟩)
      · rfl
      · exact h
  have hdisj : Disjoint diagonal (offDiagonalCollisions f) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [diagonal, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨x, rfl⟩ := hp
    exact (Finset.mem_filter.mp hq).2.2 rfl
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  congr 1
  dsimp [diagonal]
  rw [Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro x y h
    exact congrArg Prod.fst h

/-- The DC-subtracted energy is exactly the off-diagonal accident count. -/
theorem fiberEnergy_sub_card_eq_offDiagonal
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) :
    fiberEnergy f - Fintype.card X = (offDiagonalCollisions f).card := by
  rw [fiberEnergy_eq_card_collisionPairs, card_collisionPairs_eq_card_add_offDiagonal]
  omega

/-- **Literal quantitative accident floor.** -/
theorem offDiagonalAccident_dcFloor
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) :
    Fintype.card X * (Fintype.card X - Fintype.card Y) ≤
      Fintype.card Y * (offDiagonalCollisions f).card := by
  rw [← fiberEnergy_sub_card_eq_offDiagonal]
  exact dcExcess_floor f

/-- If the source outnumbers the target, at least one literal off-diagonal accident exists. -/
theorem offDiagonalCollisions_nonempty_of_card_lt
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y)
    (hcard : Fintype.card Y < Fintype.card X) :
    (offDiagonalCollisions f).Nonempty := by
  apply Finset.card_pos.mp
  rw [← fiberEnergy_sub_card_eq_offDiagonal]
  have hlt := card_lt_fiberEnergy_of_card_lt f hcard
  omega

#print axioms fiberEnergy_eq_card_collisionPairs
#print axioms card_collisionPairs_eq_card_add_offDiagonal
#print axioms fiberEnergy_sub_card_eq_offDiagonal
#print axioms offDiagonalAccident_dcFloor
#print axioms offDiagonalCollisions_nonempty_of_card_lt

end ArkLib.ProximityGap.Frontier.G141OffDiagonalAccidentIdentity
