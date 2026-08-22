/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# R288: cubic subconvexity socket

R35 rewrites the full quadratic convolution energy as a lag-correlation energy.  That
identity is correct, but the zero lag is too large at prize scale, so spending an `L^2`
bound on the quadratic convolution is not the preferred route to the R23 input.

This lightweight socket records the updated target: prove the cubic Jacobi convolution
estimate directly, or prove a cancellation package strong enough to imply it without first
paying for the zero-lag quadratic profile.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R288CubicSubconvexitySocket

/-- A pair/lag route has already produced a constant-scale quadratic budget.  This is useful
when available, but at prize scale it is stronger than what the current evidence suggests. -/
structure QuadraticLagBudget where
  constantScaleSelfConv : Prop

/-- Direct cubic subconvexity for the punctured Jacobi convolution.  This is the R23-scale
target `sum_d |J*J*J(d)|^2 <= C m^3 q^3`, kept abstract here to avoid importing the heavy
Jacobi cone. -/
structure CubicSubconvexity where
  tripleConvEnergy : Prop

/-- A cancellation package that keeps the final convolution phase instead of taking absolute
values at the quadratic stage. -/
structure FinalPhaseCancellation where
  connectedSixPointCancellation : Prop
  diagonalWickBookkeeping : Prop

/-- The old lag route can still package the cubic target when its unusually strong quadratic
budget is supplied. -/
def cubic_of_quadraticLagBudget (h : QuadraticLagBudget) :
    CubicSubconvexity :=
  ⟨h.constantScaleSelfConv⟩

/-- The preferred R288 route: prove the connected six-point cancellation and diagonal
bookkeeping directly, then consume them as cubic subconvexity. -/
def cubic_of_finalPhaseCancellation (h : FinalPhaseCancellation) :
    CubicSubconvexity :=
  ⟨h.connectedSixPointCancellation ∧ h.diagonalWickBookkeeping⟩

/-- The proof path selector used by the workbench after R288. -/
structure CubicRoutePackage where
  cubic : CubicSubconvexity
  avoidsQuadraticAbsoluteValueSpend : Prop

/-- Final-phase cancellation gives the route package without assuming a quadratic lag budget. -/
def cubicRoutePackage_of_finalPhaseCancellation (h : FinalPhaseCancellation) :
    CubicRoutePackage :=
  ⟨cubic_of_finalPhaseCancellation h, True⟩

end ArkLib.ProximityGap.Frontier.R288CubicSubconvexitySocket

open ArkLib.ProximityGap.Frontier.R288CubicSubconvexitySocket in
#print axioms cubic_of_quadraticLagBudget
open ArkLib.ProximityGap.Frontier.R288CubicSubconvexitySocket in
#print axioms cubic_of_finalPhaseCancellation
open ArkLib.ProximityGap.Frontier.R288CubicSubconvexitySocket in
#print axioms cubicRoutePackage_of_finalPhaseCancellation
