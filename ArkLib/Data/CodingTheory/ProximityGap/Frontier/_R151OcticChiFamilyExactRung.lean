/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R19ExplicitCharacterRung
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R149OcticFullRungPipeline

/-!
# LANE B2 (#466 round 151): octic pipeline feeds the explicit `chiFamily` exact rung

R149 packages the order-8 superelliptic/Stepanov route as a producer of
`FourthMomentTwistBound`.  R19 packages the explicit-character decomposition for the full
`chiFamily χ`, with only the normalized size gate and fourth-moment input left to callers.

This file composes those two public APIs.  The full-family normalized gate is known to be
impossible in the large-order route (R24), so these consumers are mainly a clean audit surface
and a template for thinned-family variants.  No prize closure is claimed.
-/

namespace ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung

open Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.ConstantIndexGaussSum
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R18SigmaEquidistribution
open ArkLib.ProximityGap.Frontier.R19ChiDecomposition
open ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter
open ArkLib.ProximityGap.Frontier.R148OcticDStepanovAdapter
open ArkLib.ProximityGap.Frontier.R149OcticFullRungPipeline
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The octic superelliptic pipeline supplies the R17 fourth-moment input for the explicit
`chiFamily χ` exact-rung consumers. -/
theorem fourthMomentTwistBound_chiFamily_of_octic_superelliptic
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (χ : MulChar F ℂ) (G : Finset F)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hq_odd : Odd (Fintype.card F)) (h8 : 8 ∣ (Fintype.card F - 1))
    (hm : ∀ χ' ∈ chiFamily χ, 0 < msteps χ')
    (hJ : ∀ χ' ∈ chiFamily χ, 0 < J χ')
    (hT1 : ∀ χ' ∈ chiFamily χ, ∀ c ∈ T χ', ‖c‖ = 1)
    (hT0 : ∀ χ' ∈ chiFamily χ, (∑ c ∈ T χ', c) = 0)
    (hvals : ∀ χ' ∈ chiFamily χ, ∀ u v w s : F,
      tripleVal χ' u v w s = 0 ∨ tripleVal χ' u v w s ∈ T χ')
    (hmodel : ∀ χ' ∈ chiFamily χ,
      ClassFiberPowerModel χ' (T χ') (e χ') (gOf χ') (ζOf χ'))
    (hpoly : ∀ χ' ∈ chiFamily χ,
      OcticModelPolynomialHypotheses (F := F) (T χ') (gOf χ'))
    (he : ∀ χ' ∈ chiFamily χ, e χ' = (Fintype.card F - 1) / 8)
    (hmq : ∀ χ' ∈ chiFamily χ, msteps χ' < Fintype.card F)
    (hD : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      8 * D χ' + 7 * (gOf χ' u v w c).natDegree < Fintype.card F)
    (hcount : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      msteps χ' * (D χ' + ((gOf χ' u v w c).natDegree - 1) * msteps χ' + J χ')
        < 8 * (J χ' * (D χ' + 1)))
    (hDtot : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      (gOf χ' u v w c).natDegree * (msteps χ' + (8 - 1) * e χ') + D χ'
          + Fintype.card F * (J χ' - 1) ≤ Dtot χ')
    (harith : ∀ χ' ∈ chiFamily χ,
      ((T χ').card : ℝ) * ((Dtot χ' : ℝ) / (msteps χ' : ℝ)) - (Fintype.card F : ℝ) + 3
        ≤ Cd χ' * Real.sqrt (Fintype.card F))
    (hCd0 : ∀ χ' ∈ chiFamily χ, 0 ≤ Cd χ')
    (hCdmax : ∀ χ' ∈ chiFamily χ, Cd χ' ≤ Cmax)
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound
      G (chiFamily χ) (4 + Cmax) :=
  fourthMomentTwistBound_of_octic_superelliptic_pipeline G (chiFamily χ) T msteps e J D
    Dtot Cd gOf ζOf hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount
    hDtot harith hCd0 hCdmax hn4q

/-- The octic superelliptic pipeline also supplies the fourth-moment input for any thinned
subfamily `Y ⊆ chiFamily χ`.  This is the usable form for the residual/thinning route, since the
full `chiFamily` size gate is known to be impossible in the large-order regime. -/
theorem fourthMomentTwistBound_chiSubfamily_of_octic_superelliptic
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (χ : MulChar F ℂ) (G : Finset F) {Y : Finset (MulChar F ℂ)}
    (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hq_odd : Odd (Fintype.card F)) (h8 : 8 ∣ (Fintype.card F - 1))
    (hm : ∀ χ' ∈ chiFamily χ, 0 < msteps χ')
    (hJ : ∀ χ' ∈ chiFamily χ, 0 < J χ')
    (hT1 : ∀ χ' ∈ chiFamily χ, ∀ c ∈ T χ', ‖c‖ = 1)
    (hT0 : ∀ χ' ∈ chiFamily χ, (∑ c ∈ T χ', c) = 0)
    (hvals : ∀ χ' ∈ chiFamily χ, ∀ u v w s : F,
      tripleVal χ' u v w s = 0 ∨ tripleVal χ' u v w s ∈ T χ')
    (hmodel : ∀ χ' ∈ chiFamily χ,
      ClassFiberPowerModel χ' (T χ') (e χ') (gOf χ') (ζOf χ'))
    (hpoly : ∀ χ' ∈ chiFamily χ,
      OcticModelPolynomialHypotheses (F := F) (T χ') (gOf χ'))
    (he : ∀ χ' ∈ chiFamily χ, e χ' = (Fintype.card F - 1) / 8)
    (hmq : ∀ χ' ∈ chiFamily χ, msteps χ' < Fintype.card F)
    (hD : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      8 * D χ' + 7 * (gOf χ' u v w c).natDegree < Fintype.card F)
    (hcount : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      msteps χ' * (D χ' + ((gOf χ' u v w c).natDegree - 1) * msteps χ' + J χ')
        < 8 * (J χ' * (D χ' + 1)))
    (hDtot : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      (gOf χ' u v w c).natDegree * (msteps χ' + (8 - 1) * e χ') + D χ'
          + Fintype.card F * (J χ' - 1) ≤ Dtot χ')
    (harith : ∀ χ' ∈ chiFamily χ,
      ((T χ').card : ℝ) * ((Dtot χ' : ℝ) / (msteps χ' : ℝ)) - (Fintype.card F : ℝ) + 3
        ≤ Cd χ' * Real.sqrt (Fintype.card F))
    (hCd0 : ∀ χ' ∈ chiFamily χ, 0 ≤ Cd χ')
    (hCdmax : ∀ χ' ∈ chiFamily χ, Cd χ' ≤ Cmax)
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound
      G Y (4 + Cmax) :=
  fourthMomentTwistBound_mono hY
    (fourthMomentTwistBound_chiFamily_of_octic_superelliptic χ G T msteps e J D Dtot Cd
      gOf ζOf hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith
      hCd0 hCdmax hn4q)

/-- Thinned-family exact-rung consumer with the fourth-moment input supplied by the octic
superelliptic pipeline.  The remaining nontrivial thinning input is the exact
`ChiDecompositionOff` identity for the chosen subfamily `Y`. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_constant_le_one
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * (Y.card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) Dset Y (fun χ' => gaussSum χ' ψ) (orderOf χ))
    (hq_odd : Odd (Fintype.card F)) (h8 : 8 ∣ (Fintype.card F - 1))
    (hm : ∀ χ' ∈ chiFamily χ, 0 < msteps χ')
    (hJ : ∀ χ' ∈ chiFamily χ, 0 < J χ')
    (hT1 : ∀ χ' ∈ chiFamily χ, ∀ c ∈ T χ', ‖c‖ = 1)
    (hT0 : ∀ χ' ∈ chiFamily χ, (∑ c ∈ T χ', c) = 0)
    (hvals : ∀ χ' ∈ chiFamily χ, ∀ u v w s : F,
      tripleVal χ' u v w s = 0 ∨ tripleVal χ' u v w s ∈ T χ')
    (hmodel : ∀ χ' ∈ chiFamily χ,
      ClassFiberPowerModel χ' (T χ') (e χ') (gOf χ') (ζOf χ'))
    (hpoly : ∀ χ' ∈ chiFamily χ,
      OcticModelPolynomialHypotheses (F := F) (T χ') (gOf χ'))
    (he : ∀ χ' ∈ chiFamily χ, e χ' = (Fintype.card F - 1) / 8)
    (hmq : ∀ χ' ∈ chiFamily χ, msteps χ' < Fintype.card F)
    (hD : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      8 * D χ' + 7 * (gOf χ' u v w c).natDegree < Fintype.card F)
    (hcount : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      msteps χ' * (D χ' + ((gOf χ' u v w c).natDegree - 1) * msteps χ' + J χ')
        < 8 * (J χ' * (D χ' + 1)))
    (hDtot : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      (gOf χ' u v w c).natDegree * (msteps χ' + (8 - 1) * e χ') + D χ'
          + Fintype.card F * (J χ' - 1) ≤ Dtot χ')
    (harith : ∀ χ' ∈ chiFamily χ,
      ((T χ').card : ℝ) * ((Dtot χ' : ℝ) / (msteps χ' : ℝ)) - (Fintype.card F : ℝ) + 3
        ≤ Cd χ' * Real.sqrt (Fintype.card F))
    (hCd0 : ∀ χ' ∈ chiFamily χ, 0 ≤ Cd χ')
    (hCdmax : ∀ χ' ∈ chiFamily χ, Cd χ' ≤ Cmax)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) Dset 2 := by
  have h4 :
      ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound
        G Y (4 + Cmax) :=
    fourthMomentTwistBound_chiSubfamily_of_octic_superelliptic χ G hY T msteps e J D Dtot
      Cd gOf ζOf hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot
      harith hCd0 hCdmax hn4q
  exact wickForIncidenceAwayAt_two_of_gchi_of_constant_le_one ψ hψ G Dset Y
    (fun χ' => gaussSum χ' ψ) χ hmord hn hCw0 hC hdec
    (gaussSumSizeBound_chiSubfamily χ hψ hY) h4 hq1 hnq hreg

/-- Raw-fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_constant_le_one`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_constant_le_one
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * (Y.card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) Dset Y (fun χ' => gaussSum χ' ψ) (orderOf χ))
    (hq_odd : Odd (Fintype.card F)) (h8 : 8 ∣ (Fintype.card F - 1))
    (hm : ∀ χ' ∈ chiFamily χ, 0 < msteps χ')
    (hJ : ∀ χ' ∈ chiFamily χ, 0 < J χ')
    (hT1 : ∀ χ' ∈ chiFamily χ, ∀ c ∈ T χ', ‖c‖ = 1)
    (hT0 : ∀ χ' ∈ chiFamily χ, (∑ c ∈ T χ', c) = 0)
    (hvals : ∀ χ' ∈ chiFamily χ, ∀ u v w s : F,
      tripleVal χ' u v w s = 0 ∨ tripleVal χ' u v w s ∈ T χ')
    (hmodel : ∀ χ' ∈ chiFamily χ,
      ClassFiberPowerModel χ' (T χ') (e χ') (gOf χ') (ζOf χ'))
    (hpoly : ∀ χ' ∈ chiFamily χ,
      OcticModelPolynomialHypotheses (F := F) (T χ') (gOf χ'))
    (he : ∀ χ' ∈ chiFamily χ, e χ' = (Fintype.card F - 1) / 8)
    (hmq : ∀ χ' ∈ chiFamily χ, msteps χ' < Fintype.card F)
    (hD : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      8 * D χ' + 7 * (gOf χ' u v w c).natDegree < Fintype.card F)
    (hcount : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      msteps χ' * (D χ' + ((gOf χ' u v w c).natDegree - 1) * msteps χ' + J χ')
        < 8 * (J χ' * (D χ' + 1)))
    (hDtot : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      (gOf χ' u v w c).natDegree * (msteps χ' + (8 - 1) * e χ') + D χ'
          + Fintype.card F * (J χ' - 1) ≤ Dtot χ')
    (harith : ∀ χ' ∈ chiFamily χ,
      ((T χ').card : ℝ) * ((Dtot χ' : ℝ) / (msteps χ' : ℝ)) - (Fintype.card F : ℝ) + 3
        ≤ Cd χ' * Real.sqrt (Fintype.card F))
    (hCd0 : ∀ χ' ∈ chiFamily χ, 0 ≤ Cd χ')
    (hCdmax : ∀ χ' ∈ chiFamily χ, Cd χ' ≤ Cmax)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) Dset := by
  exact (wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal G (Gchi χ) Dset).mp
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_constant_le_one
      ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hCw0 hC hdec
      hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hq1 hnq hn4q hreg)

/-- The octic superelliptic pipeline supplies the fourth-moment hypothesis needed by the
explicit `chiFamily` exact-rung consumer.  The normalized full-family gate is kept as an
explicit hypothesis, matching R19. -/
theorem wickForIncidenceAwayAt_two_of_chiFamily_octic_superelliptic_of_constant_le_one
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hq_odd : Odd (Fintype.card F)) (h8 : 8 ∣ (Fintype.card F - 1))
    (hm : ∀ χ' ∈ chiFamily χ, 0 < msteps χ')
    (hJ : ∀ χ' ∈ chiFamily χ, 0 < J χ')
    (hT1 : ∀ χ' ∈ chiFamily χ, ∀ c ∈ T χ', ‖c‖ = 1)
    (hT0 : ∀ χ' ∈ chiFamily χ, (∑ c ∈ T χ', c) = 0)
    (hvals : ∀ χ' ∈ chiFamily χ, ∀ u v w s : F,
      tripleVal χ' u v w s = 0 ∨ tripleVal χ' u v w s ∈ T χ')
    (hmodel : ∀ χ' ∈ chiFamily χ,
      ClassFiberPowerModel χ' (T χ') (e χ') (gOf χ') (ζOf χ'))
    (hpoly : ∀ χ' ∈ chiFamily χ,
      OcticModelPolynomialHypotheses (F := F) (T χ') (gOf χ'))
    (he : ∀ χ' ∈ chiFamily χ, e χ' = (Fintype.card F - 1) / 8)
    (hmq : ∀ χ' ∈ chiFamily χ, msteps χ' < Fintype.card F)
    (hD : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      8 * D χ' + 7 * (gOf χ' u v w c).natDegree < Fintype.card F)
    (hcount : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      msteps χ' * (D χ' + ((gOf χ' u v w c).natDegree - 1) * msteps χ' + J χ')
        < 8 * (J χ' * (D χ' + 1)))
    (hDtot : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      (gOf χ' u v w c).natDegree * (msteps χ' + (8 - 1) * e χ') + D χ'
          + Fintype.card F * (J χ' - 1) ≤ Dtot χ')
    (harith : ∀ χ' ∈ chiFamily χ,
      ((T χ').card : ℝ) * ((Dtot χ' : ℝ) / (msteps χ' : ℝ)) - (Fintype.card F : ℝ) + 3
        ≤ Cd χ' * Real.sqrt (Fintype.card F))
    (hCd0 : ∀ χ' ∈ chiFamily χ, 0 ≤ Cd χ')
    (hCdmax : ∀ χ' ∈ chiFamily χ, Cd χ' ≤ Cmax)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) Dset 2 := by
  have h4 :
      ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound
        G (chiFamily χ) (4 + Cmax) :=
    fourthMomentTwistBound_chiFamily_of_octic_superelliptic χ G T msteps e J D Dtot Cd gOf ζOf
      hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hn4q
  exact wickForIncidenceAwayAt_two_of_chiFamily_of_constant_le_one ψ hψ χ G Dset hmord hn hGD
    hCw0 hC h4 hq1 hnq hreg

/-- Raw-fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiFamily_octic_superelliptic_of_constant_le_one`. -/
theorem rawFourthMomentWithDiagonal_of_chiFamily_octic_superelliptic_of_constant_le_one
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hq_odd : Odd (Fintype.card F)) (h8 : 8 ∣ (Fintype.card F - 1))
    (hm : ∀ χ' ∈ chiFamily χ, 0 < msteps χ')
    (hJ : ∀ χ' ∈ chiFamily χ, 0 < J χ')
    (hT1 : ∀ χ' ∈ chiFamily χ, ∀ c ∈ T χ', ‖c‖ = 1)
    (hT0 : ∀ χ' ∈ chiFamily χ, (∑ c ∈ T χ', c) = 0)
    (hvals : ∀ χ' ∈ chiFamily χ, ∀ u v w s : F,
      tripleVal χ' u v w s = 0 ∨ tripleVal χ' u v w s ∈ T χ')
    (hmodel : ∀ χ' ∈ chiFamily χ,
      ClassFiberPowerModel χ' (T χ') (e χ') (gOf χ') (ζOf χ'))
    (hpoly : ∀ χ' ∈ chiFamily χ,
      OcticModelPolynomialHypotheses (F := F) (T χ') (gOf χ'))
    (he : ∀ χ' ∈ chiFamily χ, e χ' = (Fintype.card F - 1) / 8)
    (hmq : ∀ χ' ∈ chiFamily χ, msteps χ' < Fintype.card F)
    (hD : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      8 * D χ' + 7 * (gOf χ' u v w c).natDegree < Fintype.card F)
    (hcount : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      msteps χ' * (D χ' + ((gOf χ' u v w c).natDegree - 1) * msteps χ' + J χ')
        < 8 * (J χ' * (D χ' + 1)))
    (hDtot : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      (gOf χ' u v w c).natDegree * (msteps χ' + (8 - 1) * e χ') + D χ'
          + Fintype.card F * (J χ' - 1) ≤ Dtot χ')
    (harith : ∀ χ' ∈ chiFamily χ,
      ((T χ').card : ℝ) * ((Dtot χ' : ℝ) / (msteps χ' : ℝ)) - (Fintype.card F : ℝ) + 3
        ≤ Cd χ' * Real.sqrt (Fintype.card F))
    (hCd0 : ∀ χ' ∈ chiFamily χ, 0 ≤ Cd χ')
    (hCdmax : ∀ χ' ∈ chiFamily χ, Cd χ' ≤ Cmax)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) Dset := by
  have h4 :
      ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound
        G (chiFamily χ) (4 + Cmax) :=
    fourthMomentTwistBound_chiFamily_of_octic_superelliptic χ G T msteps e J D Dtot Cd gOf ζOf
      hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hn4q
  exact rawFourthMomentWithDiagonal_of_chiFamily_of_constant_le_one ψ hψ χ G Dset hmord hn hGD
    hCw0 hC h4 hq1 hnq hreg

/-- Direct off-diagonal incidence consumer for the octic `chiFamily` exact rung, specialized to
the available `r = 2` Wick certificate. -/
theorem incidence_le_of_chiFamily_octic_superelliptic_of_constant_le_one
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hq_odd : Odd (Fintype.card F)) (h8 : 8 ∣ (Fintype.card F - 1))
    (hm : ∀ χ' ∈ chiFamily χ, 0 < msteps χ')
    (hJ : ∀ χ' ∈ chiFamily χ, 0 < J χ')
    (hT1 : ∀ χ' ∈ chiFamily χ, ∀ c ∈ T χ', ‖c‖ = 1)
    (hT0 : ∀ χ' ∈ chiFamily χ, (∑ c ∈ T χ', c) = 0)
    (hvals : ∀ χ' ∈ chiFamily χ, ∀ u v w s : F,
      tripleVal χ' u v w s = 0 ∨ tripleVal χ' u v w s ∈ T χ')
    (hmodel : ∀ χ' ∈ chiFamily χ,
      ClassFiberPowerModel χ' (T χ') (e χ') (gOf χ') (ζOf χ'))
    (hpoly : ∀ χ' ∈ chiFamily χ,
      OcticModelPolynomialHypotheses (F := F) (T χ') (gOf χ'))
    (he : ∀ χ' ∈ chiFamily χ, e χ' = (Fintype.card F - 1) / 8)
    (hmq : ∀ χ' ∈ chiFamily χ, msteps χ' < Fintype.card F)
    (hD : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      8 * D χ' + 7 * (gOf χ' u v w c).natDegree < Fintype.card F)
    (hcount : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      msteps χ' * (D χ' + ((gOf χ' u v w c).natDegree - 1) * msteps χ' + J χ')
        < 8 * (J χ' * (D χ' + 1)))
    (hDtot : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      (gOf χ' u v w c).natDegree * (msteps χ' + (8 - 1) * e χ') + D χ'
          + Fintype.card F * (J χ' - 1) ≤ Dtot χ')
    (harith : ∀ χ' ∈ chiFamily χ,
      ((T χ').card : ℝ) * ((Dtot χ' : ℝ) / (msteps χ' : ℝ)) - (Fintype.card F : ℝ) + 3
        ≤ Cd χ' * Real.sqrt (Fintype.card F))
    (hCd0 : ∀ χ' ∈ chiFamily χ, 0 ≤ Cd χ')
    (hCdmax : ∀ χ' ∈ chiFamily χ, Cd χ' ≤ Cmax)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hdepth : 2 = ⌈Real.log (Fintype.card F : ℝ)⌉₊)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidenceSum
        ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1
        * (∑ b ∈ (Gchi χ), ‖ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta
          ψ G b‖ ^ 2) * (2 : ℕ)) :=
  incidence_le_of_wickAwayAt (ψ := ψ) G (Gchi χ) Dset 2 hdepth (by norm_num) hq1
    (wickForIncidenceAwayAt_two_of_chiFamily_octic_superelliptic_of_constant_le_one
      ψ hψ χ G Dset T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hC
      hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hq1 hnq hn4q hreg)
    hs

/-- Sup-norm approximate-`B` consumer for the octic `chiFamily` exact rung. -/
theorem approxB_away_of_chiFamily_octic_superelliptic_of_constant_le_one
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [NeZero (2 : FractionRing (Polynomial (Polynomial F)))]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hq_odd : Odd (Fintype.card F)) (h8 : 8 ∣ (Fintype.card F - 1))
    (hm : ∀ χ' ∈ chiFamily χ, 0 < msteps χ')
    (hJ : ∀ χ' ∈ chiFamily χ, 0 < J χ')
    (hT1 : ∀ χ' ∈ chiFamily χ, ∀ c ∈ T χ', ‖c‖ = 1)
    (hT0 : ∀ χ' ∈ chiFamily χ, (∑ c ∈ T χ', c) = 0)
    (hvals : ∀ χ' ∈ chiFamily χ, ∀ u v w s : F,
      tripleVal χ' u v w s = 0 ∨ tripleVal χ' u v w s ∈ T χ')
    (hmodel : ∀ χ' ∈ chiFamily χ,
      ClassFiberPowerModel χ' (T χ') (e χ') (gOf χ') (ζOf χ'))
    (hpoly : ∀ χ' ∈ chiFamily χ,
      OcticModelPolynomialHypotheses (F := F) (T χ') (gOf χ'))
    (he : ∀ χ' ∈ chiFamily χ, e χ' = (Fintype.card F - 1) / 8)
    (hmq : ∀ χ' ∈ chiFamily χ, msteps χ' < Fintype.card F)
    (hD : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      8 * D χ' + 7 * (gOf χ' u v w c).natDegree < Fintype.card F)
    (hcount : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      msteps χ' * (D χ' + ((gOf χ' u v w c).natDegree - 1) * msteps χ' + J χ')
        < 8 * (J χ' * (D χ' + 1)))
    (hDtot : ∀ χ' ∈ chiFamily χ, ∀ u v w : F, ∀ c ∈ T χ',
      (gOf χ' u v w c).natDegree * (msteps χ' + (8 - 1) * e χ') + D χ'
          + Fintype.card F * (J χ' - 1) ≤ Dtot χ')
    (harith : ∀ χ' ∈ chiFamily χ,
      ((T χ').card : ℝ) * ((Dtot χ' : ℝ) / (msteps χ' : ℝ)) - (Fintype.card F : ℝ) + 3
        ≤ Cd χ' * Real.sqrt (Fintype.card F))
    (hCd0 : ∀ χ' ∈ chiFamily χ, 0 ≤ Cd χ')
    (hCdmax : ∀ χ' ∈ chiFamily χ, Cd χ' ≤ Cmax)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hdepth : 2 = ⌈Real.log (Fintype.card F : ℝ)⌉₊)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ (Gchi χ),
      ‖ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidenceSum
        ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (((Gchi χ).card : ℝ) * M ^ 2) * (2 : ℕ)) :=
  approxB_away_of_wickAwayAt (ψ := ψ) G (Gchi χ) Dset 2 hdepth (by norm_num) hq1
    (wickForIncidenceAwayAt_two_of_chiFamily_octic_superelliptic_of_constant_le_one
      ψ hψ χ G Dset T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hC
      hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hq1 hnq hn4q hreg)
    hM0 hM hs

end ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms fourthMomentTwistBound_chiFamily_of_octic_superelliptic
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms fourthMomentTwistBound_chiSubfamily_of_octic_superelliptic
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_constant_le_one
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_constant_le_one
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms wickForIncidenceAwayAt_two_of_chiFamily_octic_superelliptic_of_constant_le_one
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms rawFourthMomentWithDiagonal_of_chiFamily_octic_superelliptic_of_constant_le_one
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms incidence_le_of_chiFamily_octic_superelliptic_of_constant_le_one
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms approxB_away_of_chiFamily_octic_superelliptic_of_constant_le_one
