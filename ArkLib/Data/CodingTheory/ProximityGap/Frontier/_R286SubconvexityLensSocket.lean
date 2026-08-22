/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R286 subconvexity lens socket)
-/
import Mathlib.Data.Real.Basic

/-!
# R286 (#466): subconvexity lens socket

This lightweight socket records the updated attack shape without importing the
full coding stack:

* `SupNormSubconvex` is the Paley/BGK period bound.
* `HyperplaneSubconvex` is the BCHKS-style far-line incidence cancellation.
* The prize floor consumes the pair, not either input alone.

The concrete in-tree consumer is
`ProximityGap.Frontier.PrizeFloorOfBGK.prizeFloor_of_BGK_and_incidence`; this
file is only the abstract bookkeeping layer.
-/

namespace ProximityGap.Frontier.R286SubconvexityLensSocket

/-- Abstract name for the BGK/Paley period sup-norm subconvexity input. -/
def SupNormSubconvex (Ω : Type*) : Prop := Nonempty Ω

/-- Abstract name for the hyperplane/far-line incidence subconvexity input. -/
def HyperplaneSubconvex (Ω : Type*) : Prop := Nonempty Ω

/-- Abstract name for the prize-floor conclusion supplied by the existing
`WorstCaseIncidenceBounded` consumer. -/
def PrizeFloor (Ω : Type*) : Prop := Nonempty Ω

/-- The subconvexity package consists of both period sup-norm subconvexity and
the separate hyperplane-incidence upgrade. -/
def SubconvexityPackage (Ω : Type*) : Prop :=
  SupNormSubconvex Ω ∧ HyperplaneSubconvex Ω

/-- A package pins the prize floor once the hyperplane consumer is supplied.
The statement intentionally keeps the consumer explicit: R286's point is that
the sup-norm input alone is not enough. -/
theorem prizeFloor_of_subconvexityPackage
    (Ω : Type*) (hconsume : HyperplaneSubconvex Ω → PrizeFloor Ω)
    (hpack : SubconvexityPackage Ω) :
    PrizeFloor Ω :=
  hconsume hpack.2

end ProximityGap.Frontier.R286SubconvexityLensSocket

/-! ## Axiom audit -/
#print axioms
  ProximityGap.Frontier.R286SubconvexityLensSocket.prizeFloor_of_subconvexityPackage
