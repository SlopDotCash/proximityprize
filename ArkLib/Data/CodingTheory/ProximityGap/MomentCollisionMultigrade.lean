/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumSecondMomentCollision
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Issue #232 (ABF26) — the M2 anti-concentration → onset transition in the smooth hierarchy.

`MomentCollisionSubgroupData.lean` pinned `M2 = collisionCount` at its floor `C(n,a)` for the order-`8`
subgroup of `F₁₇` at `a = 3` (the `(∑x, ∑x²)` statistic is injective there). This file proves the
**other direction** at the next level up.

* `collisionCount_gt_choose_of_offDiagonal` — the structural converse of `collisionCount_eq_of_injOn`:
  a single witnessed off-diagonal collision (two *distinct* `a`-subsets sharing `∑x` and `∑x²`) forces
  `collisionCount G a > C(|G|, a)` — the collision set strictly contains the diagonal.
* `F17star_collisionCount_gt_floor` — **the transition.** The Prouhet–Tarry–Escott multigrade
  `{1,5,6}` / `{2,3,7}` (equal `∑x = 12`, equal `∑x² = 62`) consists of two distinct `3`-subsets of the
  full order-`16` group `F₁₇* = {1,…,16}` (a smooth `2⁴` domain), so `collisionCount F17star 3 > C(16,3)`.
  But `5, 6, 3, 7` are quadratic non-residues, so this multigrade is **absent** from the order-`8`
  subgroup `G17` (`MomentCollisionSubgroupData`), which sits at the floor. So the off-diagonal of `M2`
  switches on between the order-`8` and order-`16` smooth subgroups of `F₁₇` — a machine-checked
  anti-concentration → concentration-onset transition.

## Honest scope

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`; plain `decide` over the explicit
witness sets, not the `C(16,3)²` product). A small concrete instance illustrating that `M2` does leave
its floor as the smooth domain grows; not a quantitative bound on `M2`, which remains the open
Weil-on-curves content.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators
open ArkLib.ProximityGap.Round7SecondMoment

namespace ArkLib.ProximityGap.MomentCollisionMultigrade

variable {F : Type*} [Field F] [DecidableEq F]

/-- **A witnessed off-diagonal collision puts M2 strictly above its floor.** If two *distinct*
`a`-subsets `S₀, S₀'` share `∑x` and `∑x²`, then `collisionCount G a > C(|G|, a)` — the collision set
strictly contains the diagonal. The structural converse of `collisionCount_eq_of_injOn`. -/
theorem collisionCount_gt_choose_of_offDiagonal (G : Finset F) (a : ℕ)
    {S₀ S₀' : Finset F} (hS₀ : S₀ ∈ G.powersetCard a) (hS₀' : S₀' ∈ G.powersetCard a)
    (hne : S₀ ≠ S₀') (h1 : (∑ x ∈ S₀, x) = (∑ x ∈ S₀', x))
    (h2 : (∑ x ∈ S₀, x ^ 2) = (∑ x ∈ S₀', x ^ 2)) :
    (G.card).choose a < collisionCount G a := by
  unfold collisionCount
  rw [← Finset.card_powersetCard a G]
  set cs := (G.powersetCard a ×ˢ G.powersetCard a).filter
    (fun p => (∑ x ∈ p.1, x) = (∑ x ∈ p.2, x) ∧ (∑ x ∈ p.1, x ^ 2) = (∑ x ∈ p.2, x ^ 2)) with hcs
  set D := (G.powersetCard a).image (fun S => (S, S)) with hD
  have hinj : Set.InjOn (fun S : Finset F => (S, S)) (↑(G.powersetCard a) : Set (Finset F)) := by
    intro S₁ _ S₂ _ h; exact (Prod.mk.injEq _ _ _ _ ▸ h).1
  have hDsub : D ⊆ cs := by
    intro p hp
    rw [hD, Finset.mem_image] at hp
    obtain ⟨S, hS, rfl⟩ := hp
    rw [hcs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hS, hS⟩, rfl, rfl⟩
  have hDcard : D.card = (G.powersetCard a).card := by
    rw [hD]; exact Finset.card_image_of_injOn hinj
  have hwit : (S₀, S₀') ∈ cs := by
    rw [hcs, Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hS₀, hS₀'⟩, h1, h2⟩
  have hwit_notD : (S₀, S₀') ∉ D := by
    rw [hD, Finset.mem_image]
    rintro ⟨S, _, heq⟩
    rw [Prod.mk.injEq] at heq
    exact hne (heq.1.symm.trans heq.2)
  have hssub : D ⊂ cs := (Finset.ssubset_iff_of_subset hDsub).mpr ⟨(S₀, S₀'), hwit, hwit_notD⟩
  calc (G.powersetCard a).card = D.card := hDcard.symm
    _ < cs.card := Finset.card_lt_card hssub

/-! ## The transition witness: the multigrade lives in the order-16 group, not the order-8 subgroup. -/

instance primeFact_MomentCollisionMultigrade_1 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The full order-`16` multiplicative group `F₁₇* = ⟨3⟩` (`= {1,…,16}`), a smooth `2⁴` domain. -/
def F17star : Finset (ZMod 17) := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}

theorem F17star_card : F17star.card = 16 := by decide

/-- **M2 is ABOVE its floor for the order-16 group `F₁₇*`.** The Prouhet–Tarry–Escott multigrade
`{1,5,6}` / `{2,3,7}` (equal `∑x = 12` and equal `∑x² = 62`) consists of two distinct `3`-subsets of
`F₁₇*`, so `collisionCount F17star 3 > C(16, 3) = 560`. Contrast `MomentCollisionSubgroupData`: the
*order-8 subgroup* `G17` (the quadratic residues, which exclude `5, 6, 3, 7`) has **no** such
multigrade and sits at the floor. So the off-diagonal of `M2` switches on between the order-`8` and
order-`16` smooth subgroups of `F₁₇` — a machine-checked anti-concentration → concentration-onset
transition in the smooth hierarchy. -/
theorem F17star_collisionCount_gt_floor :
    (F17star.card).choose 3 < collisionCount F17star 3 := by
  refine collisionCount_gt_choose_of_offDiagonal F17star 3
    (S₀ := {1, 5, 6}) (S₀' := {2, 3, 7}) ?_ ?_ ?_ ?_ ?_
  · exact Finset.mem_powersetCard.mpr ⟨by decide, by decide⟩
  · exact Finset.mem_powersetCard.mpr ⟨by decide, by decide⟩
  · decide
  · decide
  · decide

end ArkLib.ProximityGap.MomentCollisionMultigrade

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.MomentCollisionMultigrade.collisionCount_gt_choose_of_offDiagonal
#print axioms ArkLib.ProximityGap.MomentCollisionMultigrade.F17star_collisionCount_gt_floor
