/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R149OcticFullRungPipeline
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R16DiagonalExactValue

/-!
# LANE B2 (#466 round 150): octic models feed the corrected r = 2 incidence rung

R149 turns an order-8 superelliptic class-fiber model into the family-level
`FourthMomentTwistBound G X (4 + Cmax)`.  R17 consumes any `FourthMomentTwistBound`, together
with the standard χ-decomposition/Gauss/Σ arithmetic, to produce the corrected r = 2
away-incidence Wick interface.

This file composes those two APIs.  It does not close the deep tower; it makes the octic
Stepanov route a direct producer for the established r = 2 incidence consumers.
-/

namespace ArkLib.ProximityGap.Frontier.R150OcticR2WeilConsumer

open Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R16DiagonalExactValue
open ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter
open ArkLib.ProximityGap.Frontier.R148OcticDStepanovAdapter
open ArkLib.ProximityGap.Frontier.R149OcticFullRungPipeline

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Octic superelliptic class-fiber certificates produce the R17 fourth-moment twist input
with constant `4 + Cmax`. -/
theorem fourthMomentTwistBound_of_octic_superelliptic_consumer
    (G : Finset F) (X : Finset (MulChar F ℂ))
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    FourthMomentTwistBound G X (4 + Cmax) :=
  fourthMomentTwistBound_of_octic_superelliptic_pipeline G X T msteps e J D Dtot Cd gOf ζOf
    h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
    hCdmax hp

/-- Octic superelliptic class-fiber certificates, plus the standard R17 decomposition inputs,
produce the corrected `r = 2` away-incidence Wick rung. -/
theorem wickAwayAtWithConstant_two_of_octic_superelliptic_pipeline
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hSig : (G.card : ℝ) * (Fintype.card F : ℝ)
        ≤ 2 * (mχ : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    WickAwayAtWithConstant ψ G H Dset 2
      (32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3) := by
  have h4 :
      FourthMomentTwistBound G X (4 + Cmax) :=
    fourthMomentTwistBound_of_octic_superelliptic_consumer G X T msteps e J D Dtot Cd gOf ζOf
      h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hp
  exact wickAwayAtWithConstant_two_of_weil ψ G H Dset X g mχ hmχ hCw0 hdec hg h4
    hq1 hnq hSig

/-- Exact R15 away-Wick companion to
`wickAwayAtWithConstant_two_of_octic_superelliptic_pipeline` in the constant-`≤ 1` regime. -/
theorem wickForIncidenceAwayAt_two_of_octic_superelliptic_pipeline_le_one
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hCle : 32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3 ≤ 1)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hSig : (G.card : ℝ) * (Fintype.card F : ℝ)
        ≤ 2 * (mχ : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    WickForIncidenceAwayAt ψ G H Dset 2 :=
  wickForIncidenceAwayAt_of_wickAwayAtWithConstant_le_one G H Dset 2 hCle
    (wickAwayAtWithConstant_two_of_octic_superelliptic_pipeline ψ G H Dset X g mχ
      T msteps e J D Dtot Cd gOf ζOf hmχ hCw0 hdec hg hq1 hnq hSig h8 hm hJ
      hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0 hCdmax hp)

/-- Raw-fourth-moment companion to
`wickAwayAtWithConstant_two_of_octic_superelliptic_pipeline` in the constant-`≤ 1` regime. -/
theorem rawFourthMomentWithDiagonal_of_octic_superelliptic_pipeline_le_one
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hCle : 32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3 ≤ 1)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hSig : (G.card : ℝ) * (Fintype.card F : ℝ)
        ≤ 2 * (mχ : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    RawFourthMomentWithDiagonal ψ G H Dset :=
  rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one G H Dset hCle
    (wickAwayAtWithConstant_two_of_octic_superelliptic_pipeline ψ G H Dset X g mχ
      T msteps e J D Dtot Cd gOf ζOf hmχ hCw0 hdec hg hq1 hnq hSig h8 hm hJ
      hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0 hCdmax hp)

/-- Pointwise fourth-root incidence consumer produced by the octic superelliptic pipeline. -/
theorem incidence_sq_le_sqrt_of_octic_superelliptic_pipeline
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hSig : (G.card : ℝ) * (Fintype.card F : ℝ)
        ≤ 2 * (mχ : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G H s₀‖ ^ 2
      ≤ Real.sqrt ((32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2)
          * ((Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2)) := by
  have h4 :
      FourthMomentTwistBound G X (4 + Cmax) :=
    fourthMomentTwistBound_of_octic_superelliptic_consumer G X T msteps e J D Dtot Cd gOf ζOf
      h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hp
  exact incidence_sq_le_sqrt_of_weil_r2 ψ G H Dset X g mχ hmχ hCw0 hdec hg h4
    hq1 hnq hSig hs

/-- Sup-norm variant of the pointwise incidence consumer produced by the octic pipeline.

This is the direct R149→R17 bridge for routes that first prove a pointwise envelope
`‖eta ψ G b‖ ≤ M` on `H`, rather than keeping the raw second moment. -/
theorem incidence_sq_le_sqrt_sup_of_octic_superelliptic_pipeline
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hSig : (G.card : ℝ) * (Fintype.card F : ℝ)
        ≤ 2 * (mχ : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G H s₀‖ ^ 2
      ≤ Real.sqrt ((32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2)
          * ((Fintype.card F : ℝ) * ((H.card : ℝ) * M ^ 2) ^ 2)) := by
  have h4 :
      FourthMomentTwistBound G X (4 + Cmax) :=
    fourthMomentTwistBound_of_octic_superelliptic_consumer G X T msteps e J D Dtot Cd gOf ζOf
      h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hp
  exact incidence_sq_le_sqrt_sup_of_weil_r2 ψ G H Dset X g mχ hmχ hCw0 hdec hg h4
    hq1 hnq hSig hM0 hM hs

/-- Direct norm incidence consumer produced by the octic superelliptic pipeline.

This composes the R150 `r = 2` constant-aware Wick certificate with the R16 off-diagonal
incidence bridge, leaving the calibrated depth equality explicit. -/
theorem incidence_le_of_octic_superelliptic_pipeline
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hCge : 1 ≤ 32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hSig : (G.card : ℝ) * (Fintype.card F : ℝ)
        ≤ 2 * (mχ : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hdepth : 2 =
      ⌈Real.log ((32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3)
        * (Fintype.card F : ℝ))⌉₊)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * (2 : ℕ)) :=
  incidence_le_of_wickAwayAtWithConstant G H Dset hCge hq1 2 hdepth (by norm_num)
    (wickAwayAtWithConstant_two_of_octic_superelliptic_pipeline ψ G H Dset X g mχ
      T msteps e J D Dtot Cd gOf ζOf hmχ hCw0 hdec hg hq1 hnq hSig h8 hm hJ
      hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0 hCdmax hp)
    hs

/-- Sup-norm approximate-`B` consumer produced by the octic superelliptic pipeline. -/
theorem approxB_away_of_octic_superelliptic_pipeline
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hCge : 1 ≤ 32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hSig : (G.card : ℝ) * (Fintype.card F : ℝ)
        ≤ 2 * (mχ : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hdepth : 2 =
      ⌈Real.log ((32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3)
        * (Fintype.card F : ℝ))⌉₊)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * ((H.card : ℝ) * M ^ 2) * (2 : ℕ)) :=
  approxB_away_of_wickAwayAtWithConstant G H Dset hCge hq1 2 hdepth (by norm_num)
    (wickAwayAtWithConstant_two_of_octic_superelliptic_pipeline ψ G H Dset X g mχ
      T msteps e J D Dtot Cd gOf ζOf hmχ hCw0 hdec hg hq1 hnq hSig h8 hm hJ
      hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0 hCdmax hp)
    hM0 hM hs

end ArkLib.ProximityGap.Frontier.R150OcticR2WeilConsumer

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R150OcticR2WeilConsumer in
#print axioms fourthMomentTwistBound_of_octic_superelliptic_consumer
open ArkLib.ProximityGap.Frontier.R150OcticR2WeilConsumer in
#print axioms wickAwayAtWithConstant_two_of_octic_superelliptic_pipeline
open ArkLib.ProximityGap.Frontier.R150OcticR2WeilConsumer in
#print axioms wickForIncidenceAwayAt_two_of_octic_superelliptic_pipeline_le_one
open ArkLib.ProximityGap.Frontier.R150OcticR2WeilConsumer in
#print axioms rawFourthMomentWithDiagonal_of_octic_superelliptic_pipeline_le_one
open ArkLib.ProximityGap.Frontier.R150OcticR2WeilConsumer in
#print axioms incidence_sq_le_sqrt_of_octic_superelliptic_pipeline
open ArkLib.ProximityGap.Frontier.R150OcticR2WeilConsumer in
#print axioms incidence_sq_le_sqrt_sup_of_octic_superelliptic_pipeline
open ArkLib.ProximityGap.Frontier.R150OcticR2WeilConsumer in
#print axioms incidence_le_of_octic_superelliptic_pipeline
open ArkLib.ProximityGap.Frontier.R150OcticR2WeilConsumer in
#print axioms approxB_away_of_octic_superelliptic_pipeline
