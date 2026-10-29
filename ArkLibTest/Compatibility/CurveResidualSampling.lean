/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/

import ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.BCIKS20.Curves

/-!
# PMF residuals retain their finite-field interface

The native curve conclusions quantify `SampleableType`. These historical PMF residuals and
their counting bridge use only the finite-field assumptions below. A section-wide native sampler
can accidentally become an additional parameter through typeclass inference; this client catches
that interface regression.
-/

namespace ArkLibTest.Compatibility.CurveResidualSampling

open ProximityGap
open scoped NNReal

variable {ι F : Type} [Fintype ι] [Nonempty ι] [Field F] [Fintype F] [DecidableEq F]
variable {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}

example : Prop :=
  StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ)

example : Prop :=
  StrictCanonicalCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ)

example : Prop :=
  BoundaryProbabilityResidual (k := k) (deg := deg) (domain := domain) (δ := δ)

/-- The PMF boundary-count bridge needs no native sampler instance. -/
theorem boundary_probability_of_card [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hc : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryProbabilityResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  boundaryProbabilityResidual_of_boundaryCardResidual hδ hc

/--
info: 'ArkLibTest.Compatibility.CurveResidualSampling.boundary_probability_of_card'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms boundary_probability_of_card

end ArkLibTest.Compatibility.CurveResidualSampling
