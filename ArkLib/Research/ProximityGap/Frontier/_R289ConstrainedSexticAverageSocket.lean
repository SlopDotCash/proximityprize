/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.ZMod.Basic

/-!
# R289: constrained sextic average socket

R37 gives a pointwise exact formula for balanced six-`J` correlations.  The cubic
triple-convolution energy, however, does not sum an unconstrained five-dimensional lag box:
after parameterizing

`x = j+t`, `y = j+t+a`, `z = j+t+b`, `x' = j`, `y' = j+a'`, `z' = j+b'`,

the convolution condition `x+y+z=x'+y'+z'` becomes

`3*t + a + b = a' + b'`.

This file records the resulting proof socket: the desired subconvexity input is a
constrained average over that hyperplane, not a uniform all-lag sextic supremum.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R289ConstrainedSexticAverageSocket

variable {m : ℕ} [NeZero m]

/-- The lag hyperplane imposed by equality of the two triple-convolution indices. -/
def CubicLagConstraint (a b a' b' t : ZMod m) : Prop :=
  3 • t + a + b = a' + b'

/-- The constrained average subconvexity input: the R37 six-correlation family has the
needed cancellation after summing over the convolution hyperplane. -/
structure ConstrainedSexticAverageSubconvex
    (Corr : ZMod m → ZMod m → ZMod m → ZMod m → ZMod m → Prop) where
  hyperplaneAverage :
    ∀ a b a' b' t : ZMod m, CubicLagConstraint a b a' b' t → Corr a b a' b' t

/-- Direct cubic subconvexity for the Jacobi triple convolution, kept abstract to avoid
importing the heavy R23/R37 cone in this socket. -/
structure CubicTripleConvSubconvex where
  tripleConvEnergy : Prop

/-- A bridge theorem saying the constrained six-correlation average is strong enough to
bound the cubic convolution energy.  Future heavier files should replace the abstract
`bridge` field by the explicit expansion proof. -/
structure ConstrainedAverageBridge
    (Corr : ZMod m → ZMod m → ZMod m → ZMod m → ZMod m → Prop) where
  bridge :
    ConstrainedSexticAverageSubconvex Corr → CubicTripleConvSubconvex

/-- Consuming the constrained average through the bridge gives cubic subconvexity without
spending a uniform all-lag supremum. -/
def cubicTripleConvSubconvex_of_constrainedAverage
    {Corr : ZMod m → ZMod m → ZMod m → ZMod m → ZMod m → Prop}
    (hbridge : ConstrainedAverageBridge Corr)
    (havg : ConstrainedSexticAverageSubconvex Corr) :
    CubicTripleConvSubconvex :=
  hbridge.bridge havg

/-- The R289 route package records both the cubic result and the fact that the convolution
hyperplane was retained. -/
structure ConstrainedCubicRoute
    (Corr : ZMod m → ZMod m → ZMod m → ZMod m → ZMod m → Prop) where
  cubic : CubicTripleConvSubconvex
  usesCubicLagConstraint : Prop
  localInput : ConstrainedSexticAverageSubconvex Corr

/-- Package form of the constrained-average route. -/
def constrainedCubicRoute_of_average
    {Corr : ZMod m → ZMod m → ZMod m → ZMod m → ZMod m → Prop}
    (hbridge : ConstrainedAverageBridge Corr)
    (havg : ConstrainedSexticAverageSubconvex Corr) :
    ConstrainedCubicRoute Corr :=
  ⟨cubicTripleConvSubconvex_of_constrainedAverage hbridge havg, True, havg⟩

end ArkLib.ProximityGap.Frontier.R289ConstrainedSexticAverageSocket

open ArkLib.ProximityGap.Frontier.R289ConstrainedSexticAverageSocket in
#print axioms CubicLagConstraint
open ArkLib.ProximityGap.Frontier.R289ConstrainedSexticAverageSocket in
#print axioms cubicTripleConvSubconvex_of_constrainedAverage
open ArkLib.ProximityGap.Frontier.R289ConstrainedSexticAverageSocket in
#print axioms constrainedCubicRoute_of_average
