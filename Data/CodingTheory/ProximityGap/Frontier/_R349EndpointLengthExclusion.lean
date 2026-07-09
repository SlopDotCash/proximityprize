/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R324KernelRelationLengthStratification

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R349EndpointLengthExclusion

open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope
open ArkLib.ProximityGap.Frontier.R324KernelRelationLengthStratification

theorem relationCancellationStratum_eq_empty_of_endpointL1_gt
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r s L : ℕ)
    (hL : 2 * r - 2 * s < L)
    (hmin : ∀ d : Fin m → ℤ,
      d ∈ shadowKernelRelations g (2 * m) m r → L ≤ endpointL1 d) :
    relationCancellationStratum g m r s = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro d hd
  have hdecomp := decomposition_of_mem_relationCancellationStratum g m r s hd
  have hmin' := hmin d (Finset.mem_filter.mp hd).1
  have hcalc : endpointL1 d = 2 * r - 2 * s := by
    omega
  omega

end ArkLib.ProximityGap.Frontier.R349EndpointLengthExclusion

#print axioms
  ArkLib.ProximityGap.Frontier.R349EndpointLengthExclusion.relationCancellationStratum_eq_empty_of_endpointL1_gt
