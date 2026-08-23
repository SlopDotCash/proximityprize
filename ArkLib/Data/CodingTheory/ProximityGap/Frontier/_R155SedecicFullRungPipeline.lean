/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24FullRungAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R154SedecicDStepanovAdapter

/-!
# LANE B2 (#466 round 155): sedecic model to the r = 2 fourth-moment face

R154 turns an order-16 tuple/class superelliptic model into `DStepanovOutput`.  R24's
full-rung assembly turns per-character `DStepanovOutput`, class-value facts, and explicit
constant arithmetic into `FourthMomentTwistBound`.

This file is the sedecic analogue of the octic R149 pipeline.  It leaves the concrete
class-value facts, class-to-power-fiber model, and numerical budgets explicit, while
discharging the order-16 norm-fold independence input internally through R26/R154.
-/

namespace ArkLib.ProximityGap.Frontier.R155SedecicFullRungPipeline

open Polynomial
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter
open ArkLib.ProximityGap.Frontier.R154SedecicDStepanovAdapter

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Sedecic full-rung pipeline.**  A family of order-16 superelliptic class-fiber models,
with the usual class-value facts and explicit Stepanov arithmetic, supplies the r = 2
fourth-moment face at constant `4 + Cmax`.  The order-16 norm-fold independence is
discharged internally by R26 through the R154 adapter. -/
theorem fourthMomentTwistBound_of_sedecic_superelliptic_pipeline
    (G : Finset F) (X : Finset (MulChar F ℂ))
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (h16 : 16 ∣ (Fintype.card F - 1))
    (hm : ∀ χ ∈ X, 0 < msteps χ)
    (hJ : ∀ χ ∈ X, 0 < J χ)
    (hT1 : ∀ χ ∈ X, ∀ c ∈ T χ, ‖c‖ = 1)
    (hT0 : ∀ χ ∈ X, (∑ c ∈ T χ, c) = 0)
    (hvals : ∀ χ ∈ X, ∀ u v w s : F,
      tripleVal χ u v w s = 0 ∨ tripleVal χ u v w s ∈ T χ)
    (hmodel : ∀ χ ∈ X,
      ClassFiberPowerModel χ (T χ) (e χ) (gOf χ) (ζOf χ))
    (hpoly : ∀ χ ∈ X,
      SedecicModelPolynomialHypotheses (F := F) (T χ) (gOf χ))
    (he : ∀ χ ∈ X, e χ = (Fintype.card F - 1) / 16)
    (hmq : ∀ χ ∈ X, msteps χ < Fintype.card F)
    (hD : ∀ χ ∈ X, ∀ u v w : F, ∀ c ∈ T χ,
      16 * D χ + 15 * (gOf χ u v w c).natDegree < Fintype.card F)
    (hcount : ∀ χ ∈ X, ∀ u v w : F, ∀ c ∈ T χ,
      msteps χ * (D χ + ((gOf χ u v w c).natDegree - 1) * msteps χ + J χ)
        < 16 * (J χ * (D χ + 1)))
    (hDtot : ∀ χ ∈ X, ∀ u v w : F, ∀ c ∈ T χ,
      (gOf χ u v w c).natDegree * (msteps χ + (16 - 1) * e χ) + D χ
          + Fintype.card F * (J χ - 1) ≤ Dtot χ)
    (harith : ∀ χ ∈ X,
      ((T χ).card : ℝ) * ((Dtot χ : ℝ) / (msteps χ : ℝ)) - (Fintype.card F : ℝ) + 3
        ≤ Cd χ * Real.sqrt (Fintype.card F))
    (hCd0 : ∀ χ ∈ X, 0 ≤ Cd χ)
    (hCdmax : ∀ χ ∈ X, Cd χ ≤ Cmax)
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    FourthMomentTwistBound G X (4 + Cmax) := by
  refine fourthMomentTwistBound_of_dStepanov_pipeline G X T msteps Dtot Cd hm hT1 hT0
    hvals ?_ harith hCd0 hCdmax hp
  intro χ hχ
  exact dStepanovOutput_of_sedecic_superelliptic_power_model χ (T χ) (gOf χ) (ζOf χ)
    (hJ χ hχ) h16 (hmodel χ hχ) (hpoly χ hχ) (he χ hχ) (hmq χ hχ)
    (hD χ hχ) (hcount χ hχ) (hDtot χ hχ)

end ArkLib.ProximityGap.Frontier.R155SedecicFullRungPipeline

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R155SedecicFullRungPipeline in
#print axioms fourthMomentTwistBound_of_sedecic_superelliptic_pipeline
