/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R155SedecicFullRungPipeline
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R16DiagonalExactValue

/-!
# LANE B2 (#466 round 156): sedecic models feed the corrected r = 2 incidence rung

R155 consumes an order-16 superelliptic class-fiber model and produces the family-level
`FourthMomentTwistBound G X (4 + Cmax)`.  R17 consumes any such fourth-moment input,
together with the standard χ-decomposition/Gauss/Σ arithmetic, to produce the corrected
r = 2 away-incidence Wick interface.

This is the first sedecic analogue of the octic R150 consumer: it exposes the R17
fourth-moment input and the constant-aware `WickAwayAtWithConstant` output.
-/

namespace ArkLib.ProximityGap.Frontier.R156SedecicR2WeilConsumer

open Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R16DiagonalExactValue
open ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter
open ArkLib.ProximityGap.Frontier.R154SedecicDStepanovAdapter
open ArkLib.ProximityGap.Frontier.R155SedecicFullRungPipeline

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Sedecic superelliptic class-fiber certificates produce the R17 fourth-moment twist input
with constant `4 + Cmax`. -/
theorem fourthMomentTwistBound_of_sedecic_superelliptic_consumer
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
    FourthMomentTwistBound G X (4 + Cmax) :=
  fourthMomentTwistBound_of_sedecic_superelliptic_pipeline G X T msteps e J D Dtot Cd gOf ζOf
    h16 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
    hCdmax hp

/-- Sedecic superelliptic class-fiber certificates, plus the standard R17 decomposition inputs,
produce the corrected `r = 2` away-incidence Wick rung. -/
theorem wickAwayAtWithConstant_two_of_sedecic_superelliptic_pipeline
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
    WickAwayAtWithConstant ψ G H Dset 2
      (32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3) := by
  have h4 :
      FourthMomentTwistBound G X (4 + Cmax) :=
    fourthMomentTwistBound_of_sedecic_superelliptic_consumer G X T msteps e J D Dtot Cd
      gOf ζOf h16 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hp
  exact wickAwayAtWithConstant_two_of_weil ψ G H Dset X g mχ hmχ hCw0 hdec hg h4
    hq1 hnq hSig

/-- Exact R15 away-Wick companion to
`wickAwayAtWithConstant_two_of_sedecic_superelliptic_pipeline` in the constant-`≤ 1` regime. -/
theorem wickForIncidenceAwayAt_two_of_sedecic_superelliptic_pipeline_le_one
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
    WickForIncidenceAwayAt ψ G H Dset 2 :=
  wickForIncidenceAwayAt_of_wickAwayAtWithConstant_le_one G H Dset 2 hCle
    (wickAwayAtWithConstant_two_of_sedecic_superelliptic_pipeline ψ G H Dset X g mχ
      T msteps e J D Dtot Cd gOf ζOf hmχ hCw0 hdec hg hq1 hnq hSig h16 hm hJ
      hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0 hCdmax hp)

/-- Raw-fourth-moment companion to
`wickAwayAtWithConstant_two_of_sedecic_superelliptic_pipeline` in the constant-`≤ 1` regime. -/
theorem rawFourthMomentWithDiagonal_of_sedecic_superelliptic_pipeline_le_one
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
    RawFourthMomentWithDiagonal ψ G H Dset :=
  rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one G H Dset hCle
    (wickAwayAtWithConstant_two_of_sedecic_superelliptic_pipeline ψ G H Dset X g mχ
      T msteps e J D Dtot Cd gOf ζOf hmχ hCw0 hdec hg hq1 hnq hSig h16 hm hJ
      hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0 hCdmax hp)

end ArkLib.ProximityGap.Frontier.R156SedecicR2WeilConsumer

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R156SedecicR2WeilConsumer in
#print axioms fourthMomentTwistBound_of_sedecic_superelliptic_consumer
open ArkLib.ProximityGap.Frontier.R156SedecicR2WeilConsumer in
#print axioms wickAwayAtWithConstant_two_of_sedecic_superelliptic_pipeline
open ArkLib.ProximityGap.Frontier.R156SedecicR2WeilConsumer in
#print axioms wickForIncidenceAwayAt_two_of_sedecic_superelliptic_pipeline_le_one
open ArkLib.ProximityGap.Frontier.R156SedecicR2WeilConsumer in
#print axioms rawFourthMomentWithDiagonal_of_sedecic_superelliptic_pipeline_le_one
