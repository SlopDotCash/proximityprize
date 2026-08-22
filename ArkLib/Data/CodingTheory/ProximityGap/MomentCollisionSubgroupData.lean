/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumSecondMomentCollision
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Issue #232 (ABF26) — a machine-checked M2 value for a real smooth domain.

The prize-deciding scalar is `M2 = collisionCount G a` (the second moment of the `(∑x, ∑x²)` count;
`SubsetSumSecondMomentCollision.lean`), sandwiched in `[C(n,a), C(n,a)²]`. `MomentCollisionRigidity.lean`
shows it sits at its floor `C(n,a)` for all `a ≤ 2` (any field), but says nothing for `a ≥ 3`. This
file pins the **actual value at `a = 3`** for an explicit prize-faithful evaluation domain, by a light
`decide` (over the statistic *image*, not the `C(8,3)²` collision product).

## Contents

* `collisionCount_eq_of_injOn`, `collisionCount_eq_of_image_card_eq` — the reusable structural converse
  of the concentration handle: if the `(∑x, ∑x²)` statistic is injective on the `a`-subsets (equiv. its
  image has `C(|G|,a)` distinct values), then `collisionCount G a = C(|G|, a)` — `M2` at its floor.
* `G17` — the order-`8` multiplicative subgroup `⟨2⟩ = {x : x⁸ = 1}` of `F₁₇`, a genuine smooth
  (power-of-two) FRI/STARK evaluation domain.
* `G17_image_card` — `decide`: the `(∑x, ∑x²)` image of the `3`-subsets of `G17` has `56 = C(8,3)`
  distinct values.
* `G17_collisionCount_at_floor` — **the data point:** `collisionCount G17 3 = 56`. The `(∑x, ∑x²)`
  statistic is **injective on `3`-subsets** of this real subgroup — `M2` is maximally anti-concentrated
  (the prize-favourable regime) even at `a = 3`, *beyond* the rigidity guarantee. Equivalently, this
  subgroup contains no Prouhet–Tarry–Escott multigrade of size `3` (no two disjoint `3`-subsets with
  equal `∑x` and equal `∑x²`). A first machine-checked M2 value for an explicit smooth domain.

## Honest scope

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`; plain `decide`, no
`native_decide`). This is a single small instance (`a = 3`, `|G| = 8`), data informing the open
magnitude — not a general bound on `M2`, which remains the open Weil-on-curves content.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators
open ArkLib.ProximityGap.Round7SecondMoment

namespace ArkLib.ProximityGap.MomentCollisionSubgroupData

variable {F : Type*} [Field F] [DecidableEq F]

/-- **If the `(∑x, ∑x²)` statistic is injective on `a`-subsets, the collision count is at its floor**
`collisionCount G a = C(|G|, a)` (maximal anti-concentration). The structural converse of the
concentration handle: injectivity ⟹ every fiber a singleton ⟹ `M2` minimal. -/
theorem collisionCount_eq_of_injOn (G : Finset F) (a : ℕ)
    (hinj : Set.InjOn (fun S => ((∑ x ∈ S, x), (∑ x ∈ S, x ^ 2))) (↑(G.powersetCard a) : Set (Finset F))) :
    collisionCount G a = (G.card).choose a := by
  refine le_antisymm ?_ (collisionCount_ge_choose G a)
  unfold collisionCount
  rw [← Finset.card_powersetCard a G]
  apply Finset.card_le_card_of_injOn (fun p => p.1)
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    rw [Finset.mem_coe]; exact hp.1.1
  · intro p hp p' hp' h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hp'
    obtain ⟨⟨hpS, hpS'⟩, hp1, hp2⟩ := hp
    obtain ⟨⟨hp'S, hp'S'⟩, hp'1, hp'2⟩ := hp'
    have e1 : p.1 = p.2 :=
      hinj (Finset.mem_coe.mpr hpS) (Finset.mem_coe.mpr hpS') (by rw [Prod.ext_iff]; exact ⟨hp1, hp2⟩)
    have e2 : p'.1 = p'.2 :=
      hinj (Finset.mem_coe.mpr hp'S) (Finset.mem_coe.mpr hp'S')
        (by rw [Prod.ext_iff]; exact ⟨hp'1, hp'2⟩)
    have h' : p.1 = p'.1 := h
    refine Prod.ext_iff.mpr ⟨h', ?_⟩
    rw [← e1, h']; exact e2

/-- The injectivity criterion in terms of the image card: if the `(∑x, ∑x²)` image of the `a`-subsets
has as many elements as there are `a`-subsets, the statistic is injective on them. -/
theorem injOn_of_image_card_eq (G : Finset F) (a : ℕ)
    (h : ((G.powersetCard a).image (fun S => ((∑ x ∈ S, x), (∑ x ∈ S, x ^ 2)))).card
          = (G.powersetCard a).card) :
    Set.InjOn (fun S => ((∑ x ∈ S, x), (∑ x ∈ S, x ^ 2))) (↑(G.powersetCard a) : Set (Finset F)) :=
  Finset.injOn_of_card_image_eq h

/-- **The collision count is at its floor whenever the image of the statistic is as large as the
domain.** Composes the two lemmas above. -/
theorem collisionCount_eq_of_image_card_eq (G : Finset F) (a : ℕ)
    (h : ((G.powersetCard a).image (fun S => ((∑ x ∈ S, x), (∑ x ∈ S, x ^ 2)))).card
          = (G.powersetCard a).card) :
    collisionCount G a = (G.card).choose a :=
  collisionCount_eq_of_injOn G a (injOn_of_image_card_eq G a h)

/-! ## The verified data point: a real smooth domain. -/

instance primeFact_MomentCollisionSubgroupData_1 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The order-`8` multiplicative subgroup `⟨2⟩ = {x : x⁸ = 1}` of `F₁₇` — a genuine smooth
(power-of-two) FRI/STARK evaluation domain. -/
def G17 : Finset (ZMod 17) := {1, 2, 4, 8, 9, 13, 15, 16}

/-- `|G17| = 8`. -/
theorem G17_card : G17.card = 8 := by decide

/-- The `(∑x, ∑x²)` image of the `3`-subsets of `G17` has `56 = C(8,3)` distinct values — verified by
`decide` (light, via the image, not the `56²` collision product). -/
theorem G17_image_card :
    ((G17.powersetCard 3).image (fun S => ((∑ x ∈ S, x), (∑ x ∈ S, x ^ 2)))).card = 56 := by
  decide

/-- **The verified M2 data point.** For the real order-`8` smooth subgroup of `F₁₇`, the
`(∑x, ∑x²)` collision count at agreement `3` is at its **floor**:

  `collisionCount G17 3 = C(8, 3) = 56`.

So the `(∑x, ∑x²)` statistic is **injective on `3`-subsets** — `M2` is maximally anti-concentrated,
the prize-favourable regime — even at `a = 3`, *beyond* the rigidity guarantee (`MomentCollisionRigidity`
only forces injectivity for `a ≤ 2`). This subgroup contains **no Prouhet–Tarry–Escott multigrade** of
size `3`: there are no two disjoint `3`-subsets with equal `∑x` and equal `∑x²`. A first machine-checked
M2 value for an explicit prize-faithful smooth domain. -/
theorem G17_collisionCount_at_floor : collisionCount G17 3 = 56 := by
  have hpc : (G17.powersetCard 3).card = 56 := by
    rw [Finset.card_powersetCard, G17_card]; decide
  have hcc : collisionCount G17 3 = G17.card.choose 3 :=
    collisionCount_eq_of_image_card_eq G17 3 (by rw [G17_image_card, hpc])
  rw [hcc, G17_card]; decide

end ArkLib.ProximityGap.MomentCollisionSubgroupData

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.MomentCollisionSubgroupData.collisionCount_eq_of_injOn
#print axioms ArkLib.ProximityGap.MomentCollisionSubgroupData.collisionCount_eq_of_image_card_eq
#print axioms ArkLib.ProximityGap.MomentCollisionSubgroupData.G17_collisionCount_at_floor
