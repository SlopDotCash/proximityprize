/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R59DStepanovSuperellipticAdapter
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R26D16

/-!
# LANE B2 (#466 round 154): sedecic superelliptic model to `DStepanovOutput`

R26 proves `DBlockIndependence` at `d = 16`, with the expected budget
`16D + 15·deg g < q`.  This file packages that result at the same public interface as the
octic R148 adapter: callers provide the class-fiber power model and ordinary polynomial
facts, while the `d = 16` norm-fold independence input is discharged internally.
-/

namespace ArkLib.ProximityGap.Frontier.R154SedecicDStepanovAdapter

open Polynomial
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R26D16
open ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The sedecic specialization of `SuperellipticModelHypotheses`: the tuple/class-indexed
polynomials are monic, squarefree, and positive-degree.  The order-16
`DBlockIndependence` component is supplied by R26. -/
def SedecicModelPolynomialHypotheses
    (T : Finset ℂ) (gOf : F → F → F → ℂ → F[X]) : Prop :=
  ∀ u v w : F, ∀ c ∈ T,
    (gOf u v w c).Monic ∧
      Squarefree (gOf u v w c) ∧
      0 < (gOf u v w c).natDegree

/-- Sedecic polynomial facts plus R26's `dBlockIndependence_sixteen` produce the full R59
structural model hypotheses at `d = 16`. -/
theorem superellipticModelHypotheses_sixteen
    (T : Finset ℂ) (gOf : F → F → F → ℂ → F[X])
    (h16 : 16 ∣ (Fintype.card F - 1))
    {D : ℕ}
    (hD : ∀ u v w : F, ∀ c ∈ T, 16 * D + 15 * (gOf u v w c).natDegree < Fintype.card F)
    (hpoly : SedecicModelPolynomialHypotheses (F := F) T gOf) :
    SuperellipticModelHypotheses (F := F) T gOf 16 (Fintype.card F) D := by
  intro u v w c hc
  obtain ⟨hmonic, hsf, hdeg⟩ := hpoly u v w c hc
  exact ⟨hmonic, hsf, hdeg,
    dBlockIndependence_sixteen (gOf u v w c) hsf hdeg h16 (hD u v w c hc)⟩

/-- Public sedecic adapter into the full-rung `DStepanovOutput` interface. -/
theorem dStepanovOutput_of_sedecic_superelliptic_power_model
    (χ : MulChar F ℂ) (T : Finset ℂ)
    {m e J D Dtot : ℕ}
    (gOf : F → F → F → ℂ → F[X]) (ζOf : F → F → F → ℂ → F)
    (hJ : 0 < J) (h16 : 16 ∣ (Fintype.card F - 1))
    (hmodel : ClassFiberPowerModel χ T e gOf ζOf)
    (hpoly : SedecicModelPolynomialHypotheses (F := F) T gOf)
    (he : e = (Fintype.card F - 1) / 16)
    (hmq : m < Fintype.card F)
    (hD : ∀ u v w : F, ∀ c ∈ T, 16 * D + 15 * (gOf u v w c).natDegree < Fintype.card F)
    (hcount : ∀ u v w : F, ∀ c ∈ T,
      m * (D + ((gOf u v w c).natDegree - 1) * m + J) < 16 * (J * (D + 1)))
    (hDtot : ∀ u v w : F, ∀ c ∈ T,
      (gOf u v w c).natDegree * (m + (16 - 1) * e) + D
          + Fintype.card F * (J - 1) ≤ Dtot) :
    DStepanovOutput χ T m Dtot :=
  dStepanovOutput_adapter χ T gOf ζOf hJ hmodel
    (superellipticModelHypotheses_sixteen T gOf h16 hD hpoly)
    he hmq hcount hDtot

end ArkLib.ProximityGap.Frontier.R154SedecicDStepanovAdapter

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R154SedecicDStepanovAdapter in
#print axioms superellipticModelHypotheses_sixteen
open ArkLib.ProximityGap.Frontier.R154SedecicDStepanovAdapter in
#print axioms dStepanovOutput_of_sedecic_superelliptic_power_model
