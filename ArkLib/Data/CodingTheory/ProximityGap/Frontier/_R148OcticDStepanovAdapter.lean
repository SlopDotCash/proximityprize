/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R59DStepanovSuperellipticAdapter
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R25D8Descent

/-!
# LANE B2 (#466 round 148): octic superelliptic model to `DStepanovOutput`

R59 adapts tuple/class-indexed superelliptic power fibers to the abstract
`DStepanovOutput` interface, but its structural hypothesis still includes an arbitrary
`DBlockIndependence` input.  R25 now proves that input for `d = 8` directly, with no
extra fraction-field/UFD instances at the consumer boundary.

This file packages the octic specialization: callers provide the class-fiber power model
and ordinary squarefree/positive-degree polynomial facts, and R25 supplies the order-8
norm-fold independence automatically.
-/

namespace ArkLib.ProximityGap.Frontier.R148OcticDStepanovAdapter

open Polynomial
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R25D8Descent
open ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The octic specialization of `SuperellipticModelHypotheses`: the tuple/class-indexed
polynomials are monic, squarefree, and positive-degree.  The order-8
`DBlockIndependence` component is supplied by the direct R25 octic descent theorem. -/
def OcticModelPolynomialHypotheses (T : Finset ℂ) (gOf : F → F → F → ℂ → F[X]) : Prop :=
  ∀ u v w : F, ∀ c ∈ T,
    (gOf u v w c).Monic ∧
      Squarefree (gOf u v w c) ∧
      0 < (gOf u v w c).natDegree

/-- Octic polynomial facts plus R25's `dBlockIndependence_eight` produce the full R59
structural model hypotheses at `d = 8`. -/
theorem superellipticModelHypotheses_eight
    (T : Finset ℂ) (gOf : F → F → F → ℂ → F[X])
    (h8 : 8 ∣ (Fintype.card F - 1))
    {D : ℕ}
    (hD : ∀ u v w : F, ∀ c ∈ T, 8 * D + 7 * (gOf u v w c).natDegree < Fintype.card F)
    (hpoly : OcticModelPolynomialHypotheses (F := F) T gOf) :
    SuperellipticModelHypotheses (F := F) T gOf 8 (Fintype.card F) D := by
  intro u v w c hc
  obtain ⟨hmonic, hsf, hdeg⟩ := hpoly u v w c hc
  exact ⟨hmonic, hsf, hdeg,
    dBlockIndependence_eight (gOf u v w c) hsf hdeg h8 (hD u v w c hc)⟩

/-- Public octic adapter into the full-rung `DStepanovOutput` interface.  This is R59's
adapter with the order-8 norm-fold independence discharged by R25. -/
theorem dStepanovOutput_of_octic_superelliptic_power_model
    (χ : MulChar F ℂ) (T : Finset ℂ)
    {m e J D Dtot : ℕ}
    (gOf : F → F → F → ℂ → F[X]) (ζOf : F → F → F → ℂ → F)
    (hJ : 0 < J) (h8 : 8 ∣ (Fintype.card F - 1))
    (hmodel : ClassFiberPowerModel χ T e gOf ζOf)
    (hpoly : OcticModelPolynomialHypotheses (F := F) T gOf)
    (he : e = (Fintype.card F - 1) / 8)
    (hmq : m < Fintype.card F)
    (hD : ∀ u v w : F, ∀ c ∈ T, 8 * D + 7 * (gOf u v w c).natDegree < Fintype.card F)
    (hcount : ∀ u v w : F, ∀ c ∈ T,
      m * (D + ((gOf u v w c).natDegree - 1) * m + J) < 8 * (J * (D + 1)))
    (hDtot : ∀ u v w : F, ∀ c ∈ T,
      (gOf u v w c).natDegree * (m + (8 - 1) * e) + D
          + Fintype.card F * (J - 1) ≤ Dtot) :
    DStepanovOutput χ T m Dtot :=
  dStepanovOutput_adapter χ T gOf ζOf hJ hmodel
    (superellipticModelHypotheses_eight T gOf h8 hD hpoly)
    he hmq hcount hDtot

end ArkLib.ProximityGap.Frontier.R148OcticDStepanovAdapter

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R148OcticDStepanovAdapter in
#print axioms superellipticModelHypotheses_eight
open ArkLib.ProximityGap.Frontier.R148OcticDStepanovAdapter in
#print axioms dStepanovOutput_of_octic_superelliptic_power_model
