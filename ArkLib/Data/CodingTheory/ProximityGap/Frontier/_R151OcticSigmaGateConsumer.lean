/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R18SigmaGate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R150OcticR2WeilConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R16DiagonalExactValue

/-!
# LANE B2 (#466 round 151): octic models with the sigma lower-envelope gate

R150 consumes an explicit `hSig` inequality.  This file pushes the same octic
fourth-moment producer through R18's `SigmaLowerEnvelope` gate, so callers can supply the
standard lower-envelope/regime package instead of the raw eta-energy inequality.
-/

namespace ArkLib.ProximityGap.Frontier.R151OcticSigmaGateConsumer

open Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R16DiagonalExactValue
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R18SigmaGate
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter
open ArkLib.ProximityGap.Frontier.R148OcticDStepanovAdapter
open ArkLib.ProximityGap.Frontier.R150OcticR2WeilConsumer

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Octic superelliptic certificates plus the Σ lower-envelope package produce the corrected
`r = 2` away-incidence Wick rung. -/
theorem wickAwayAtWithConstant_two_of_octic_sigmaLowerEnvelope
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ) (hmχ2 : 2 ≤ (mχ : ℝ)) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (mχ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hlow :
      SigmaLowerEnvelope (mχ : ℝ) (G.card : ℝ) (Fintype.card F : ℝ)
        (∑ b ∈ H, ‖eta ψ G b‖ ^ 2))
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
    WickAwayAtWithConstant ψ G H Dset 2
      (32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3) := by
  have h4 :
      FourthMomentTwistBound G X (4 + Cmax) :=
    fourthMomentTwistBound_of_octic_superelliptic_consumer G X T msteps e J D Dtot Cd gOf ζOf
      hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hp
  exact wickAwayAtWithConstant_two_of_weil_of_sigmaLowerEnvelope ψ G H Dset X g
    hmχ hmχ2 hn hCw0 hdec hg h4 hq1 hnq hreg hlow

/-- Exact R15 away-Wick companion to the sigma-gated octic `r = 2` Wick consumer in the
constant-`≤ 1` regime. -/
theorem wickForIncidenceAwayAt_two_of_octic_sigmaLowerEnvelope_le_one
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ) (hmχ2 : 2 ≤ (mχ : ℝ)) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hCle : 32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3 ≤ 1)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (mχ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hlow :
      SigmaLowerEnvelope (mχ : ℝ) (G.card : ℝ) (Fintype.card F : ℝ)
        (∑ b ∈ H, ‖eta ψ G b‖ ^ 2))
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
    WickForIncidenceAwayAt ψ G H Dset 2 :=
  wickForIncidenceAwayAt_of_wickAwayAtWithConstant_le_one G H Dset 2 hCle
    (wickAwayAtWithConstant_two_of_octic_sigmaLowerEnvelope ψ G H Dset X g mχ
      T msteps e J D Dtot Cd gOf ζOf hmχ hmχ2 hn hCw0 hdec hg hq1 hnq hreg hlow
      hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hp)

/-- Raw-fourth-moment companion to the sigma-gated octic `r = 2` Wick consumer in the
constant-`≤ 1` regime.  This is the lower-envelope version of
`rawFourthMomentWithDiagonal_of_octic_superelliptic_pipeline_le_one`. -/
theorem rawFourthMomentWithDiagonal_of_octic_sigmaLowerEnvelope_le_one
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ) (hmχ2 : 2 ≤ (mχ : ℝ)) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hCle : 32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3 ≤ 1)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (mχ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hlow :
      SigmaLowerEnvelope (mχ : ℝ) (G.card : ℝ) (Fintype.card F : ℝ)
        (∑ b ∈ H, ‖eta ψ G b‖ ^ 2))
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
    RawFourthMomentWithDiagonal ψ G H Dset :=
  rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one G H Dset hCle
    (wickAwayAtWithConstant_two_of_octic_sigmaLowerEnvelope ψ G H Dset X g mχ
      T msteps e J D Dtot Cd gOf ζOf hmχ hmχ2 hn hCw0 hdec hg hq1 hnq hreg hlow
      hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hp)

/-- Pointwise fourth-root incidence consumer from octic superelliptic certificates plus the
Σ lower-envelope package. -/
theorem incidence_sq_le_sqrt_of_octic_sigmaLowerEnvelope
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ) (hmχ2 : 2 ≤ (mχ : ℝ)) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (mχ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hlow :
      SigmaLowerEnvelope (mχ : ℝ) (G.card : ℝ) (Fintype.card F : ℝ)
        (∑ b ∈ H, ‖eta ψ G b‖ ^ 2))
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
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G H s₀‖ ^ 2
      ≤ Real.sqrt ((32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2)
          * ((Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2)) := by
  have h4 :
      FourthMomentTwistBound G X (4 + Cmax) :=
    fourthMomentTwistBound_of_octic_superelliptic_consumer G X T msteps e J D Dtot Cd gOf ζOf
      hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hp
  exact incidence_sq_le_sqrt_of_weil_r2 ψ G H Dset X g mχ hmχ hCw0 hdec hg h4 hq1 hnq
    (hSig_of_sigmaLowerEnvelope_field ψ G H hmχ2 hn hreg hlow) hs

/-- Sup-norm variant of the sigma-gated pointwise incidence consumer.

This is the R151 sibling of `incidence_sq_le_sqrt_sup_of_octic_superelliptic_pipeline`: callers
that have a pointwise envelope on the additive spectrum can use the standard sigma lower-envelope
package without manually reopening the raw `hSig` inequality. -/
theorem incidence_sq_le_sqrt_sup_of_octic_sigmaLowerEnvelope
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ) (hmχ2 : 2 ≤ (mχ : ℝ)) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (mχ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hlow :
      SigmaLowerEnvelope (mχ : ℝ) (G.card : ℝ) (Fintype.card F : ℝ)
        (∑ b ∈ H, ‖eta ψ G b‖ ^ 2))
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
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G H s₀‖ ^ 2
      ≤ Real.sqrt ((32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2)
          * ((Fintype.card F : ℝ) * ((H.card : ℝ) * M ^ 2) ^ 2)) := by
  exact incidence_sq_le_sqrt_sup_of_octic_superelliptic_pipeline ψ G H Dset X g mχ
    T msteps e J D Dtot Cd gOf ζOf hmχ hCw0 hdec hg hq1 hnq
    (hSig_of_sigmaLowerEnvelope_field ψ G H hmχ2 hn hreg hlow)
    hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
    hCdmax hp hM0 hM hs

/-- Direct norm incidence consumer from the octic sigma-gated `r = 2` Wick certificate.

The constant in the `r = 2` rung is paid by the caller through the standard R16 depth contract,
specialized to the available octic rung. -/
theorem incidence_le_of_octic_sigmaLowerEnvelope
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ) (hmχ2 : 2 ≤ (mχ : ℝ)) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hCge : 1 ≤ 32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (mχ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hlow :
      SigmaLowerEnvelope (mχ : ℝ) (G.card : ℝ) (Fintype.card F : ℝ)
        (∑ b ∈ H, ‖eta ψ G b‖ ^ 2))
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
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hdepth : 2 =
      ⌈Real.log ((32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3)
        * (Fintype.card F : ℝ))⌉₊)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * (2 : ℕ)) :=
  incidence_le_of_wickAwayAtWithConstant G H Dset hCge hq1 2 hdepth (by norm_num)
    (wickAwayAtWithConstant_two_of_octic_sigmaLowerEnvelope ψ G H Dset X g mχ
      T msteps e J D Dtot Cd gOf ζOf hmχ hmχ2 hn hCw0 hdec hg hq1 hnq hreg hlow
      hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hp)
    hs

/-- Sup-norm approximate-`B` consumer from the octic sigma-gated `r = 2` Wick certificate. -/
theorem approxB_away_of_octic_sigmaLowerEnvelope
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (G H Dset : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (mχ : ℕ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmχ : 1 ≤ mχ) (hmχ2 : 2 ≤ (mχ : ℝ)) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hCge : 1 ≤ 32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3)
    (hdec : ChiDecompositionOff ψ G H Dset X g mχ)
    (hg : GaussSumSizeBound X g)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (mχ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hlow :
      SigmaLowerEnvelope (mχ : ℝ) (G.card : ℝ) (Fintype.card F : ℝ)
        (∑ b ∈ H, ‖eta ψ G b‖ ^ 2))
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
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hdepth : 2 =
      ⌈Real.log ((32 * ((4 + Cmax) * (X.card : ℝ) ^ 4 + 1) / (mχ : ℝ) ^ 2 / 3)
        * (Fintype.card F : ℝ))⌉₊)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * ((H.card : ℝ) * M ^ 2) * (2 : ℕ)) :=
  approxB_away_of_wickAwayAtWithConstant G H Dset hCge hq1 2 hdepth (by norm_num)
    (wickAwayAtWithConstant_two_of_octic_sigmaLowerEnvelope ψ G H Dset X g mχ
      T msteps e J D Dtot Cd gOf ζOf hmχ hmχ2 hn hCw0 hdec hg hq1 hnq hreg hlow
      hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hp)
    hM0 hM hs

end ArkLib.ProximityGap.Frontier.R151OcticSigmaGateConsumer

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R151OcticSigmaGateConsumer in
#print axioms wickAwayAtWithConstant_two_of_octic_sigmaLowerEnvelope
open ArkLib.ProximityGap.Frontier.R151OcticSigmaGateConsumer in
#print axioms wickForIncidenceAwayAt_two_of_octic_sigmaLowerEnvelope_le_one
open ArkLib.ProximityGap.Frontier.R151OcticSigmaGateConsumer in
#print axioms rawFourthMomentWithDiagonal_of_octic_sigmaLowerEnvelope_le_one
open ArkLib.ProximityGap.Frontier.R151OcticSigmaGateConsumer in
#print axioms incidence_sq_le_sqrt_of_octic_sigmaLowerEnvelope
open ArkLib.ProximityGap.Frontier.R151OcticSigmaGateConsumer in
#print axioms incidence_sq_le_sqrt_sup_of_octic_sigmaLowerEnvelope
open ArkLib.ProximityGap.Frontier.R151OcticSigmaGateConsumer in
#print axioms incidence_le_of_octic_sigmaLowerEnvelope
open ArkLib.ProximityGap.Frontier.R151OcticSigmaGateConsumer in
#print axioms approxB_away_of_octic_sigmaLowerEnvelope
