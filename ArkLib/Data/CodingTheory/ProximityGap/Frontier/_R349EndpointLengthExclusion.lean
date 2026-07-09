import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R324KernelRelationLengthStratification

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R349EndpointLengthExclusion

open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope
open ArkLib.ProximityGap.Frontier.R324KernelRelationLengthStratification
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition

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

end ArkLib.ProximityGap.Frontier.R349EndpointLengthExclusion

#print axioms
  ArkLib.ProximityGap.Frontier.R349EndpointLengthExclusion.relationCancellationStratum_eq_empty_of_endpointL1_gt
