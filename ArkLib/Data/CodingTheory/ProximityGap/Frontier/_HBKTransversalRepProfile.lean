/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031SupTransversalCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKOrderedNatProfile
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetInvariance

/-!
# Ordered HBK representation profile on a concrete coset transversal

For a concrete `IsCosetTransversal n T`, this file forms the multiplicity-aware multiset of
additive representation counts `repCount G t`, `t∈T`, and applies the canonical descending profile.
It proves antitonicity, zero-padding, and exact preservation of the transversal squared sum.

This is the concrete container consumed by the production cap-majorization lane. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.HBKTransversalRepProfile

open scoped BigOperators
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.I031DilationOrbitReduction
open HBKOrderedNatProfile

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Multiset of representation counts on a transversal, retaining repeated values. -/
def transversalRepMultiset (G T : Finset F) : Multiset ℕ :=
  T.1.map (repCount G)

/-- Canonical descending representation-count profile of the transversal. -/
def transversalRepProfile (G T : Finset F) : ℕ → ℕ :=
  orderedProfile (transversalRepMultiset G T)

@[simp] theorem transversalRepMultiset_card (G T : Finset F) :
    (transversalRepMultiset G T).card = T.card := by
  simp [transversalRepMultiset]

/-- The actual transversal profile is decreasing. -/
theorem transversalRepProfile_antitone_succ (G T : Finset F) (i : ℕ) :
    transversalRepProfile G T (i + 1) ≤ transversalRepProfile G T i :=
  orderedProfile_antitone_succ _ i

/-- The profile is zero beyond the number of cosets. -/
theorem transversalRepProfile_boundary
    (G T : Finset F) {N : ℕ} (hN : T.card ≤ N) :
    transversalRepProfile G T N = 0 := by
  apply orderedProfile_boundary
  simpa using hN

/-- Sorting preserves the exact squared transversal mass. -/
theorem sum_transversalRepProfile_sq (G T : Finset F) :
    (∑ i ∈ Finset.range T.card, transversalRepProfile G T i ^ 2) =
      ∑ t ∈ T, repCount G t ^ 2 := by
  rw [transversalRepProfile, ← transversalRepMultiset_card]
  rw [sum_orderedProfile_sq]
  simp [transversalRepMultiset]

/-- Sorting also preserves the exact first moment on the transversal. -/
theorem sum_transversalRepProfile (G T : Finset F) :
    (∑ i ∈ Finset.range T.card, transversalRepProfile G T i) =
      ∑ t ∈ T, repCount G t := by
  rw [transversalRepProfile, ← transversalRepMultiset_card]
  rw [sum_orderedProfile]
  simp [transversalRepMultiset]

end ArkLib.ProximityGap.Frontier.HBKTransversalRepProfile

#print axioms
  ArkLib.ProximityGap.Frontier.HBKTransversalRepProfile.transversalRepProfile_antitone_succ
#print axioms
  ArkLib.ProximityGap.Frontier.HBKTransversalRepProfile.sum_transversalRepProfile_sq
#print axioms
  ArkLib.ProximityGap.Frontier.HBKTransversalRepProfile.sum_transversalRepProfile
