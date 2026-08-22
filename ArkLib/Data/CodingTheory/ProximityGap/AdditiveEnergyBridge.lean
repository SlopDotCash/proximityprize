/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment

/-!
# Round 12 (Issue #232, ABF26) — bridging the two additive-energy definitions: the sharp formula
# feeds the Gauss-sum fourth moment.

Two `additiveEnergy` definitions live in the proximity-gap tree:
* `AdditiveEnergyRepBound.additiveEnergy G = ∑_{a,b∈G} repCount(a+b)` (the representation-count form,
  carrying the sharp closed form `AdditiveEnergySidonModNeg.additiveEnergy_eq_of_sidonModNeg`);
* `SubgroupGaussSumFourthMoment.addEnergy G = ∑_{y₁,y₂,y₃,y₄∈G} [y₁+y₂=y₃+y₄]` (the quadruple-count
  form, satisfying `subgroup_gaussSum_fourthMoment : ∑_b ‖η_b‖⁴ = q · addEnergy G`).

They are the **same quantity** `#{(a,b,c,d)∈G⁴ : a+b=c+d}`. This file proves
`additiveEnergy_eq_addEnergy`, unifying the two halves of the in-tree chain, and derives
`addEnergy_eq_of_sidonModNeg : addEnergy G = 3|G|² − 3|G|` — so the sharp char-0 minimal energy now
feeds **directly** into the Gauss-sum fourth-moment identity `∑_b ‖η_b‖⁴ = q · (3|G|² − 3|G|)` for a
Sidon-modulo-negation subgroup. `sorry`-free, axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

set_option linter.style.longLine false


open ArkLib.ProximityGap.AdditiveEnergyRepBound ArkLib.ProximityGap.AdditiveEnergySidonModNeg

namespace ArkLib.ProximityGap.AdditiveEnergyBridge

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The two additive-energy definitions agree.** `AdditiveEnergyRepBound.additiveEnergy G` (the
representation-count form) equals `SubgroupGaussSumFourthMoment.addEnergy G` (the quadruple-count
form): for each `(a,b)`, the inner representations of `a+b` are counted identically, since for fixed
`y₃` the unique `y₄ = a+b−y₃` realizing `a+b = y₃+y₄` lies in `G` iff `a+b−y₃ ∈ G`. -/
theorem additiveEnergy_eq_addEnergy (G : Finset F) :
    additiveEnergy G = SubgroupGaussSumFourthMoment.addEnergy G := by
  classical
  unfold additiveEnergy SubgroupGaussSumFourthMoment.addEnergy
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  unfold repCount
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun y3 _ => ?_)
  by_cases h : a + b - y3 ∈ G
  · rw [if_pos h, Finset.sum_eq_single (a + b - y3)]
    · rw [if_pos (by ring)]
    · intro y4 _ hne
      rw [if_neg (fun heq => hne (by linear_combination -heq))]
    · intro hnot; exact absurd h hnot
  · rw [if_neg h, Finset.sum_eq_zero]
    intro y4 hy4
    rw [if_neg (fun heq => h (by
      rw [show a + b - y3 = y4 from by linear_combination heq]; exact hy4))]

/-- **The sharp energy in the Gauss-sum `addEnergy` notation.** For a Sidon-modulo-negation subgroup,
`addEnergy G = 3|G|² − 3|G|`, so the fourth-moment identity reads
`∑_b ‖η_b‖⁴ = q · (3|G|² − 3|G|)` — the sharp char-0 minimal energy fed directly into the Gauss-sum
chain. -/
theorem addEnergy_eq_of_sidonModNeg {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) (hS : SidonModNeg G) :
    SubgroupGaussSumFourthMoment.addEnergy G = 3 * G.card ^ 2 - 3 * G.card := by
  rw [← additiveEnergy_eq_addEnergy, additiveEnergy_eq_of_sidonModNeg h2 h0 hneg hS]

end ArkLib.ProximityGap.AdditiveEnergyBridge

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AdditiveEnergyBridge.additiveEnergy_eq_addEnergy
#print axioms ArkLib.ProximityGap.AdditiveEnergyBridge.addEnergy_eq_of_sidonModNeg
