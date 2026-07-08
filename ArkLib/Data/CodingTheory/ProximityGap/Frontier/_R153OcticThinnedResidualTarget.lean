/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R151OcticChiFamilyExactRung

/-!
# LANE B2 (#466 round 153): residual target for the octic thinned-family route

R151 exposes the viable octic exact-rung route for a proper subfamily
`Y ⊆ chiFamily χ`, but it asks directly for `ChiDecompositionOff` on that thinned
family.  R19 identifies that hypothesis with vanishing of the omitted-character residual.

This file packages the R151 consumer in the residual language.  It does not prove the residual
vanishes; it makes the live target explicit and prevents the remaining task from being hidden
inside a decomposition hypothesis.
-/

namespace ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget

open Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.ConstantIndexGaussSum
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R19ChiDecomposition
open ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter
open ArkLib.ProximityGap.Frontier.R148OcticDStepanovAdapter
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The R151 thinned-octic exact-rung consumer with the live decomposition hypothesis phrased
as vanishing of the omitted-character residual. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
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
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * (Y.card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y)
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
  have hdec :
      ChiDecompositionOff ψ G (Gchi χ) Dset Y (fun χ' => gaussSum χ' ψ) (orderOf χ) :=
    (chiSubfamily_chiDecompositionOff_iff_residual_vanishes χ hψ hGD hY).2 hres
  exact wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_constant_le_one
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hCw0 hC hdec
    hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
    hCdmax hq1 hnq hn4q hreg

/-- Raw-fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
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
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * (Y.card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y)
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
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
      ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hC hres
      hq_odd h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hq1 hnq hn4q hreg)

end ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
