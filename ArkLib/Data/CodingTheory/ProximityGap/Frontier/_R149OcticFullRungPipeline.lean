/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24FullRungAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R148OcticDStepanovAdapter

/-!
# LANE B2 (#466 round 149): octic model to the r = 2 fourth-moment face

R148 turns an order-8 tuple/class superelliptic model into `DStepanovOutput`.  R24's
full-rung assembly turns per-character `DStepanovOutput`, class-value facts, and explicit
constant arithmetic into `FourthMomentTwistBound`.

This file composes those two APIs.  It is deliberately honest about the remaining concrete
algebra: callers still supply the class-value set facts, the class-to-power-fiber model, and
the numerical parameter budgets.  The norm-fold independence input for `d = 8` is no longer
an open premise.
-/

namespace ArkLib.ProximityGap.Frontier.R149OcticFullRungPipeline

open Polynomial
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter
open ArkLib.ProximityGap.Frontier.R148OcticDStepanovAdapter

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Octic full-rung pipeline.**  A family of order-8 superelliptic class-fiber models,
with the usual class-value facts and explicit Stepanov arithmetic, supplies the r = 2
fourth-moment face at constant `4 + Cmax`.  The order-8 norm-fold independence is
discharged internally by R25 through the R148 adapter. -/
theorem fourthMomentTwistBound_of_octic_superelliptic_pipeline
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (G : Finset F) (X : Finset (MulChar F ℂ))
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ χ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ χ : MulChar F ℂ, F → F → F → ℂ → F)
    (hq_odd : Odd (Fintype.card F)) (h8 : 8 ∣ (Fintype.card F - 1))
    (hm : ∀ χ ∈ X, 0 < msteps χ)
    (hJ : ∀ χ ∈ X, 0 < J χ)
    (hT1 : ∀ χ ∈ X, ∀ c ∈ T χ, ‖c‖ = 1)
    (hT0 : ∀ χ ∈ X, (∑ c ∈ T χ, c) = 0)
    (hvals : ∀ χ ∈ X, ∀ u v w s : F,
      tripleVal χ u v w s = 0 ∨ tripleVal χ u v w s ∈ T χ)
    (hmodel : ∀ χ ∈ X,
      ClassFiberPowerModel χ (T χ) (e χ) (gOf χ) (ζOf χ))
    (hpoly : ∀ χ ∈ X,
      OcticModelPolynomialHypotheses (F := F) (T χ) (gOf χ))
    (he : ∀ χ ∈ X, e χ = (Fintype.card F - 1) / 8)
    (hmq : ∀ χ ∈ X, msteps χ < Fintype.card F)
    (hD : ∀ χ ∈ X, ∀ u v w : F, ∀ c ∈ T χ,
      8 * D χ + 7 * (gOf χ u v w c).natDegree < Fintype.card F)
    (hcount : ∀ χ ∈ X, ∀ u v w : F, ∀ c ∈ T χ,
      msteps χ * (D χ + ((gOf χ u v w c).natDegree - 1) * msteps χ + J χ)
        < 8 * (J χ * (D χ + 1)))
    (hDtot : ∀ χ ∈ X, ∀ u v w : F, ∀ c ∈ T χ,
      (gOf χ u v w c).natDegree * (msteps χ + (8 - 1) * e χ) + D χ
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
  exact dStepanovOutput_of_octic_superelliptic_power_model χ (T χ) (gOf χ) (ζOf χ)
    (hJ χ hχ) hq_odd h8 (hmodel χ hχ) (hpoly χ hχ) (he χ hχ) (hmq χ hχ)
    (hD χ hχ) (hcount χ hχ) (hDtot χ hχ)

end ArkLib.ProximityGap.Frontier.R149OcticFullRungPipeline

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R149OcticFullRungPipeline in
#print axioms fourthMomentTwistBound_of_octic_superelliptic_pipeline
