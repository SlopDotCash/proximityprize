/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungCoverSplit
import ArkLib.Data.CodingTheory.ProximityGap.RungSummationScaffold

/-!
# The cover assembly (#371, rung): paired scalars are covered by their classes

The missing scaffold link between `RungCoverSplit` (the solo/paired split)
and `RungSummationScaffold` (`bad_card_le_partition`).  Given ANY assignment
`cls : F → Finset F` of each paired scalar to a class-set containing it, the
paired part is covered by the (finite) family `image cls`, and the whole bad
set decomposes as `solo ∪ (classes.biUnion id)` — feeding the partition
bound directly.

* `subset_biUnion_image_of_self_mem` — the generic cover: `S ⊆ (S.image
  cls).biUnion id` when `γ ∈ cls γ` on `S`;
* `bad_card_le_via_assignment` — the assembled bound: with a class
  assignment whose classes are capped and a solo Fisher bound, the bad set
  obeys `#Γ ≤ #solo + Σ caps`.

This reduces `ClassPackingBound` to exactly two inputs, both already
isolated: a class assignment with per-class cap `n−|A|`
(`maximal_frame_attached_card_le`) and the SUM BOUND `#solo + Σ caps ≤ B`
(the open attachment-gated class count).  No new open math is introduced —
the bookkeeping half is now closed.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [DecidableEq F]

section CoverAssembly

/-- **The generic cover**: if every element of `S` lies in its assigned
class `cls γ`, then `S` is covered by the image family. -/
theorem subset_biUnion_image_of_self_mem (S : Finset F) (cls : F → Finset F)
    (hself : ∀ γ ∈ S, γ ∈ cls γ) :
    S ⊆ (S.image cls).biUnion id := by
  intro γ hγ
  rw [Finset.mem_biUnion]
  exact ⟨cls γ, Finset.mem_image_of_mem cls hγ, hself γ hγ⟩

/-- **The assembled bound**: given the solo/paired split, a class assignment
`cls` covering the paired part with each class capped by `cap`, and the
threshold `t` overlap, the bad set is bounded by `#solo + Σ caps`. -/
theorem bad_card_le_via_assignment (Γ : Finset F) {n : ℕ}
    (S : F → Finset (Fin n)) (t : ℕ) (cls : F → Finset F) (cap : Finset F → ℕ)
    (hself : ∀ γ ∈ pairedPart Γ S t, γ ∈ cls γ)
    (hcap : ∀ K ∈ (pairedPart Γ S t).image cls, K.card ≤ cap K) :
    Γ.card ≤ (soloPart Γ S t).card
      + ∑ K ∈ (pairedPart Γ S t).image cls, cap K := by
  classical
  set solo := soloPart Γ S t
  set paired := pairedPart Γ S t
  set classes := paired.image cls with hclasses
  have hcover : paired ⊆ classes.biUnion id :=
    subset_biUnion_image_of_self_mem paired cls hself
  -- Γ = solo ∪ paired ⊆ solo ∪ classes.biUnion id
  have hΓcover : Γ ⊆ solo ∪ classes.biUnion id := by
    rw [bad_eq_solo_union_paired Γ S t]
    exact Finset.union_subset_union (Finset.Subset.refl solo) hcover
  calc Γ.card ≤ (solo ∪ classes.biUnion id).card :=
        Finset.card_le_card hΓcover
    _ ≤ solo.card + (classes.biUnion id).card := Finset.card_union_le _ _
    _ ≤ solo.card + ∑ K ∈ classes, K.card := by
        have := Finset.card_biUnion_le (s := classes) (t := id)
        simp only [id_eq] at this
        omega
    _ ≤ solo.card + ∑ K ∈ classes, cap K := by
        have := Finset.sum_le_sum hcap
        omega

end CoverAssembly

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.subset_biUnion_image_of_self_mem
#print axioms ProximityGap.WBPencil.bad_card_le_via_assignment
