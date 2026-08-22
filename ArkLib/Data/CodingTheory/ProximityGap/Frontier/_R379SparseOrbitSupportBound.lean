/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R378SignedDifferenceRotationInvariance

/-!
# R379: sparse support forces a large covering orbit

This file isolates the finite combinatorial core of the rotation-orbit saving.  If a finite
family of vectors has common endpoint `L1` mass and its supports cover all `m` coordinates, then
the family has at least `m / L1` members in denominator-cleared form.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R379SparseOrbitSupportBound

open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope

/-- Nonzero coordinate support of an integer vector. -/
def vectorSupport {m : ℕ} (d : Fin m → ℤ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => d j ≠ 0)

/-- Support cardinality is at most endpoint `L1` mass. -/
theorem card_vectorSupport_le_endpointL1 {m : ℕ} (d : Fin m → ℤ) :
    (vectorSupport d).card ≤ endpointL1 d := by
  unfold vectorSupport endpointL1
  calc
    ((Finset.univ.filter fun j => d j ≠ 0).card) =
        ∑ j ∈ Finset.univ.filter (fun j => d j ≠ 0), 1 := by simp
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => d j ≠ 0), (d j).natAbs := by
      apply Finset.sum_le_sum
      intro j hj
      have hj0 : d j ≠ 0 := (Finset.mem_filter.mp hj).2
      have hjpos : 0 < (d j).natAbs := Int.natAbs_pos.mpr hj0
      omega
    _ ≤ ∑ j : Fin m, (d j).natAbs := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- A support-covering family with per-vector support cap `L` has at least `m/L` members. -/
theorem card_fin_le_family_card_mul_of_support_cover
    {m : ℕ} (O : Finset (Fin m → ℤ)) (L : ℕ)
    (hcard : ∀ d ∈ O, (vectorSupport d).card ≤ L)
    (hcover : ∀ j : Fin m, ∃ d ∈ O, d j ≠ 0) :
    m ≤ O.card * L := by
  classical
  have hsubset : (Finset.univ : Finset (Fin m)) ⊆ O.biUnion vectorSupport := by
    intro j hj
    obtain ⟨d, hdO, hdj⟩ := hcover j
    exact Finset.mem_biUnion.mpr ⟨d, hdO, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdj⟩⟩
  calc
    m = (Finset.univ : Finset (Fin m)).card := by simp
    _ ≤ (O.biUnion vectorSupport).card := Finset.card_le_card hsubset
    _ ≤ ∑ d ∈ O, (vectorSupport d).card := Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ O, L := by
      apply Finset.sum_le_sum
      intro d hd
      exact hcard d hd
    _ = O.card * L := by simp

/-- **Sparse covering-orbit bound.** If every vector in a covering family has the same endpoint
`L1` mass as `d`, then `m ≤ #O * endpointL1(d)`. -/
theorem card_fin_le_family_card_mul_endpointL1
    {m : ℕ} (O : Finset (Fin m → ℤ)) (d : Fin m → ℤ)
    (hmass : ∀ e ∈ O, endpointL1 e = endpointL1 d)
    (hcover : ∀ j : Fin m, ∃ e ∈ O, e j ≠ 0) :
    m ≤ O.card * endpointL1 d := by
  apply card_fin_le_family_card_mul_of_support_cover O (endpointL1 d)
  · intro e he
    rw [← hmass e he]
    exact card_vectorSupport_le_endpointL1 e
  · exact hcover

end ArkLib.ProximityGap.Frontier.R379SparseOrbitSupportBound

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R379SparseOrbitSupportBound.card_vectorSupport_le_endpointL1
#print axioms
  ArkLib.ProximityGap.Frontier.R379SparseOrbitSupportBound.card_fin_le_family_card_mul_endpointL1
