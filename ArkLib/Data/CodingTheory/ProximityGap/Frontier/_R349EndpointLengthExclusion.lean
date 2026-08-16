/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R324KernelRelationLengthStratification

/-!
# _R349EndpointLengthExclusion

Module docstring for `_R349EndpointLengthExclusion.lean`.
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R349EndpointLengthExclusion

open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope
open ArkLib.ProximityGap.Frontier.R324KernelRelationLengthStratification
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity

theorem relationCancellationStratum_eq_empty_of_endpointL1_gt
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r s L : ℕ)
    (hL : 2 * r - 2 * s < L)
    (hmin : ∀ d : Fin m → ℤ,
      d ∈ shadowKernelRelations g (2 * m) m r → L ≤ endpointL1 d) :
    relationCancellationStratum g m r s = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hdecomp := decomposition_of_mem_relationCancellationStratum g m r s hd
  have hmin' := hmin d (Finset.mem_filter.mp hd).1
  have hcalc : endpointL1 d = 2 * r - 2 * s := by
    omega
  omega

theorem depth_four_high_strata_empty_of_endpointL1_ge_six
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m : ℕ)
    (hmin : ∀ d : Fin m → ℤ,
      d ∈ shadowKernelRelations g (2 * m) m 4 → 6 ≤ endpointL1 d)
    {s : ℕ} (hs : 2 ≤ s) :
    relationCancellationStratum g m 4 s = ∅ := by
  apply relationCancellationStratum_eq_empty_of_endpointL1_gt g m 4 s 6
  · omega
  · exact hmin

theorem shadowCollisionMass_le_depth_four_low_shells
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m : ℕ)
    (hmin : ∀ d : Fin m → ℤ,
      d ∈ shadowKernelRelations g (2 * m) m 4 → 6 ≤ endpointL1 d) :
    shadowCollisionMass g (2 * m) m 4 ≤
      Nat.factorial 8 * ((relationCancellationStratum g m 4 0).card +
        (relationCancellationStratum g m 4 1).card * m) := by
  have hbase : shadowCollisionMass g (2 * m) m 4 ≤
      Nat.factorial (4 + 4) *
        ∑ s ∈ Finset.range 4,
          (relationCancellationStratum g m 4 s).card * m ^ s :=
    shadowCollisionMass_le_factorial_mul_weighted_stratum_count g m 4
  have h2 := depth_four_high_strata_empty_of_endpointL1_ge_six g m hmin (s := 2) (by omega)
  have h3 := depth_four_high_strata_empty_of_endpointL1_ge_six g m hmin (s := 3) (by omega)
  simpa [h2, h3, Finset.sum_range_succ, Nat.factorial] using hbase

end ArkLib.ProximityGap.Frontier.R349EndpointLengthExclusion

#print axioms
  ArkLib.ProximityGap.Frontier.R349EndpointLengthExclusion.relationCancellationStratum_eq_empty_of_endpointL1_gt
