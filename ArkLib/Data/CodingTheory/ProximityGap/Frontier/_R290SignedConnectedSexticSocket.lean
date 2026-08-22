/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Real.Basic

/-!
# R290: signed connected sextic socket

R290 refines R289: after imposing the cubic lag hyperplane, the Wick-perfect-matching
bucket can exceed the desired cubic energy.  The connected sextic remainder is therefore not
an error term to bound by absolute values; it is a signed cancellation term that must be kept
in the aggregate.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R290SignedConnectedSexticSocket

/-- Abstract scalar profile for a constrained sextic expansion. -/
structure SignedSexticProfile where
  wickPerfectMatching : ℝ
  connectedRemainder : ℝ
  cubicEnergy : ℝ

/-- The exact signed decomposition of the constrained sextic expansion. -/
def SignedConnectedDecomposition (P : SignedSexticProfile) : Prop :=
  P.cubicEnergy = P.wickPerfectMatching + P.connectedRemainder

/-- The target scale for the R23 cubic subconvexity bound. -/
def CubicScaleBound (P : SignedSexticProfile) (C scale : ℝ) : Prop :=
  P.cubicEnergy ≤ C * scale

/-- Signed connected cancellation: diagonal plus connected remainder stays within the cubic
scale.  The connected term is intentionally not absolutized. -/
def SignedConnectedSexticCancellation
    (P : SignedSexticProfile) (C scale : ℝ) : Prop :=
  P.wickPerfectMatching + P.connectedRemainder ≤ C * scale

/-- Consuming the signed connected estimate through the exact decomposition. -/
theorem cubicScaleBound_of_signedConnectedCancellation
    {P : SignedSexticProfile} {C scale : ℝ}
    (hdec : SignedConnectedDecomposition P)
    (hcancel : SignedConnectedSexticCancellation P C scale) :
    CubicScaleBound P C scale := by
  unfold SignedConnectedDecomposition at hdec
  unfold SignedConnectedSexticCancellation CubicScaleBound at *
  rw [hdec]
  exact hcancel

/-- A positive-mass replacement is a different and stronger hypothesis; this marker records
that the R290 route uses the signed aggregate. -/
structure SignedConnectedRoute (P : SignedSexticProfile) (C scale : ℝ) where
  decomposition : SignedConnectedDecomposition P
  signedCancellation : SignedConnectedSexticCancellation P C scale
  cubicBound : CubicScaleBound P C scale

/-- Package the R290 route from exact decomposition and signed cancellation. -/
def signedConnectedRoute
    {P : SignedSexticProfile} {C scale : ℝ}
    (hdec : SignedConnectedDecomposition P)
    (hcancel : SignedConnectedSexticCancellation P C scale) :
    SignedConnectedRoute P C scale :=
  ⟨hdec, hcancel, cubicScaleBound_of_signedConnectedCancellation hdec hcancel⟩

end ArkLib.ProximityGap.Frontier.R290SignedConnectedSexticSocket

open ArkLib.ProximityGap.Frontier.R290SignedConnectedSexticSocket in
#print axioms cubicScaleBound_of_signedConnectedCancellation
open ArkLib.ProximityGap.Frontier.R290SignedConnectedSexticSocket in
#print axioms signedConnectedRoute
