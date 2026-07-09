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

set_option linter.style.longFile 1800

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

noncomputable local instance : DecidableEq (MulChar F ℂ) := Classical.decEq _

/-- The R151 thinned-octic exact-rung consumer with the live decomposition hypothesis phrased
as vanishing of the omitted-character residual. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
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
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
    hCdmax hq1 hnq hn4q hreg

/-- Raw-fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
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
    (h8 : 8 ∣ (Fintype.card F - 1))
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
      h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hq1 hnq hn4q hreg)

/-- Direct off-diagonal incidence consumer for the explicit-constant residual form. -/
theorem incidence_le_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
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
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1
        * (∑ b ∈ (Gchi χ), ‖eta ψ G b‖ ^ 2) * (2 : ℕ)) := by
  exact incidence_le_of_wickAwayAt (ψ := ψ) G (Gchi χ) Dset 2 hdepth (by norm_num) hq1
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
      ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hC hres
      h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hq1 hnq hn4q hreg)
    hs

/-- Sup-norm approximate-`B` consumer for the explicit-constant residual form. -/
theorem approxB_away_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
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
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ (Gchi χ), ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (((Gchi χ).card : ℝ) * M ^ 2) * (2 : ℕ)) := by
  exact approxB_away_of_wickAwayAt (ψ := ψ) G (Gchi χ) Dset 2 hdepth (by norm_num) hq1
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
      ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hC hres
      h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hq1 hnq hn4q hreg)
    hM0 hM hs

/-- Size-gated residual form of the viable thinned-octic route.  The remaining live
decomposition target is exactly residual vanishing; the normalized constant gate is discharged
from `Cmax ≤ 2`, nonempty `Y`, and `15 * |Y|² ≤ orderOf χ`. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
  exact wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_Cmax_le_two
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hCw0 hCmax2
    hYnonempty horder hdec h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
    hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg

/-- Raw-fourth-moment companion to the size-gated residual form. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
      ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
      hYnonempty horder hres h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
      hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg)

/-- Direct off-diagonal incidence consumer for the size-gated residual form. -/
theorem incidence_le_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1
        * (∑ b ∈ (Gchi χ), ‖eta ψ G b‖ ^ 2) * (2 : ℕ)) := by
  exact incidence_le_of_wickAwayAt (ψ := ψ) G (Gchi χ) Dset 2 hdepth (by norm_num) hq1
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
      ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
      hYnonempty horder hres h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
      hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg)
    hs

/-- Sup-norm approximate-`B` consumer for the size-gated residual form. -/
theorem approxB_away_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ (Gchi χ), ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (((Gchi χ).card : ℝ) * M ^ 2) * (2 : ℕ)) := by
  exact approxB_away_of_wickAwayAt (ψ := ψ) G (Gchi χ) Dset 2 hdepth (by norm_num) hq1
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
      ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
      hYnonempty horder hres h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
      hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg)
    hM0 hM hs

/-- Character-by-character sufficient condition for the R153 residual target: if every omitted
twisted thin sum vanishes off `Dset`, then the omitted-character residual vanishes off `Dset`.

This is deliberately stronger than cancellation of the omitted sum, but it isolates an exact
per-character target for attempts that choose `Y` by deleting characters with forced shifted
vanishing. -/
theorem chiSubfamilyResidualVanishesOff_of_omitted_twistedThinSum_zero
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G Dset : Finset F)
    (Y : Finset (MulChar F ℂ))
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y → twistedThinSum χ' G s₀ = 0) :
    ChiSubfamilyResidualVanishesOff χ ψ G Dset Y := by
  classical
  intro s₀ hs₀
  unfold chiSubfamilyResidual
  exact Finset.sum_eq_zero fun χ' hχ' => by
    have hmem : χ' ∈ chiFamily χ ∧ χ' ∉ Y := by
      simpa [Finset.mem_sdiff] using hχ'
    rw [homit s₀ hs₀ χ' hmem.1 hmem.2, mul_zero]

/-- Shifted-character-sum version of the omitted-zero sufficient condition.  This is the same
target as `chiSubfamilyResidualVanishesOff_of_omitted_twistedThinSum_zero`, but phrased in the
`shiftedCharSum` API used by the Tχ moment files. -/
theorem chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G Dset : Finset F)
    (Y : Finset (MulChar F ℂ))
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0) :
    ChiSubfamilyResidualVanishesOff χ ψ G Dset Y := by
  refine chiSubfamilyResidualVanishesOff_of_omitted_twistedThinSum_zero χ ψ G Dset Y ?_
  intro s₀ hs₀ χ' hχ' hχ'Y
  simp [twistedThinSum_eq_star_shiftedCharSum, homit s₀ hs₀ χ' hχ' hχ'Y]

/-- Boundary case for the thinned residual: if the retained subfamily covers all of
`chiFamily χ`, then there are no omitted characters and the residual vanishes identically. -/
theorem chiSubfamilyResidualVanishesOff_of_chiFamily_subset
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G Dset : Finset F)
    (Y : Finset (MulChar F ℂ)) (hcover : chiFamily χ ⊆ Y) :
    ChiSubfamilyResidualVanishesOff χ ψ G Dset Y := by
  classical
  intro s₀ _hs₀
  unfold chiSubfamilyResidual
  exact Finset.sum_eq_zero fun χ' hχ' => by
    have hmem : χ' ∈ chiFamily χ ∧ χ' ∉ Y := by
      simpa [Finset.mem_sdiff] using hχ'
    exact False.elim (hmem.2 (hcover hmem.1))

/-- Self-boundary case for the thinned residual: omitting nothing from `chiFamily χ` makes the
residual vanish.  R152 records why this is not the usable prize route: the full-family size gate
is impossible in the nontrivial octic regime. -/
theorem chiSubfamilyResidualVanishesOff_self
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G Dset : Finset F) :
    ChiSubfamilyResidualVanishesOff χ ψ G Dset (chiFamily χ) :=
  chiSubfamilyResidualVanishesOff_of_chiFamily_subset χ ψ G Dset (chiFamily χ) fun _ hχ => hχ

/-- Size-gated thinned-octic endpoint with the residual target discharged by pointwise
vanishing of every omitted twisted thin sum. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y → twistedThinSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
  have hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y :=
    chiSubfamilyResidualVanishesOff_of_omitted_twistedThinSum_zero χ ψ G Dset Y homit
  exact wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
    hYnonempty horder hres h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
    hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg

/-- Raw-fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y → twistedThinSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
      ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
      hYnonempty horder homit h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
      hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg)

/-- Direct off-diagonal incidence endpoint with the residual target discharged by pointwise
vanishing of every omitted twisted thin sum. -/
theorem incidence_le_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y → twistedThinSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1
        * (∑ b ∈ (Gchi χ), ‖eta ψ G b‖ ^ 2) * (2 : ℕ)) := by
  have hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y :=
    chiSubfamilyResidualVanishesOff_of_omitted_twistedThinSum_zero χ ψ G Dset Y homit
  exact incidence_le_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
    hYnonempty horder hres h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
    hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg hdepth hs

/-- Sup-norm approximate-`B` endpoint with the residual target discharged by pointwise
vanishing of every omitted twisted thin sum. -/
theorem approxB_away_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y → twistedThinSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ (Gchi χ), ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (((Gchi χ).card : ℝ) * M ^ 2) * (2 : ℕ)) := by
  have hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y :=
    chiSubfamilyResidualVanishesOff_of_omitted_twistedThinSum_zero χ ψ G Dset Y homit
  exact approxB_away_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
    hYnonempty horder hres h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
    hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg hdepth hM0 hM hs

/-- Size-gated thinned-octic endpoint with the residual target discharged by pointwise
vanishing of every omitted shifted character sum. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
  have hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y :=
    chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero χ ψ G Dset Y homit
  exact wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
    hYnonempty horder hres h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
    hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg

/-- Raw-fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
      ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
      hYnonempty horder homit h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
      hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg)

/-- Direct off-diagonal incidence endpoint with the residual target discharged by pointwise
vanishing of every omitted shifted character sum. -/
theorem incidence_le_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1
        * (∑ b ∈ (Gchi χ), ‖eta ψ G b‖ ^ 2) * (2 : ℕ)) := by
  have hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y :=
    chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero χ ψ G Dset Y homit
  exact incidence_le_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
    hYnonempty horder hres h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
    hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg hdepth hs

/-- Sup-norm approximate-`B` endpoint with the residual target discharged by pointwise
vanishing of every omitted shifted character sum. -/
theorem approxB_away_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ (Gchi χ), ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (((Gchi χ).card : ℝ) * M ^ 2) * (2 : ℕ)) := by
  have hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y :=
    chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero χ ψ G Dset Y homit
  exact approxB_away_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
    hYnonempty horder hres h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
    hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg hdepth hM0 hM hs

/-- Explicit-constant thinned-octic endpoint with the residual target discharged by pointwise
vanishing of every omitted shifted character sum. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero
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
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
  have hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y :=
    chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero χ ψ G Dset Y homit
  exact wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hC hres
    h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
    hCdmax hq1 hnq hn4q hreg

/-- Raw-fourth-moment companion for the explicit-constant shifted-zero form. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_shifted_zero
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
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero
      ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hC homit
      h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
      hCdmax hq1 hnq hn4q hreg)

/-- Direct off-diagonal incidence endpoint for the explicit-constant shifted-zero form. -/
theorem incidence_le_of_chiSubfamily_octic_superelliptic_of_shifted_zero
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
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1
        * (∑ b ∈ (Gchi χ), ‖eta ψ G b‖ ^ 2) * (2 : ℕ)) := by
  have hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y :=
    chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero χ ψ G Dset Y homit
  exact incidence_le_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hC hres
    h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
    hCdmax hq1 hnq hn4q hreg hdepth hs

/-- Sup-norm approximate-`B` endpoint for the explicit-constant shifted-zero form. -/
theorem approxB_away_of_chiSubfamily_octic_superelliptic_of_shifted_zero
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
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ (Gchi χ), ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (((Gchi χ).card : ℝ) * M ^ 2) * (2 : ℕ)) := by
  have hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y :=
    chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero χ ψ G Dset Y homit
  exact approxB_away_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hC hres
    h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD hcount hDtot harith hCd0
    hCdmax hq1 hnq hn4q hreg hdepth hM0 hM hs

/-- Size-gated thinned-octic endpoint with the residual target discharged by pointwise
vanishing in the `shiftedCharSum` API. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_omitted_shifted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
  have hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y :=
    chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero χ ψ G Dset Y homit
  exact wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
    hYnonempty horder hres h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
    hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg

/-- Raw-fourth-moment companion to the shifted-sum size-gated endpoint. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_omitted_shifted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_omitted_shifted_zero_Cmax_le_two
      ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
      hYnonempty horder homit h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
      hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg)

/-- Direct off-diagonal incidence endpoint in the shifted-sum size-gated form. -/
theorem incidence_le_of_chiSubfamily_octic_superelliptic_of_omitted_shifted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1
        * (∑ b ∈ (Gchi χ), ‖eta ψ G b‖ ^ 2) * (2 : ℕ)) := by
  have hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y :=
    chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero χ ψ G Dset Y homit
  exact incidence_le_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
    hYnonempty horder hres h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
    hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg hdepth hs

/-- Sup-norm approximate-`B` endpoint in the shifted-sum size-gated form. -/
theorem approxB_away_of_chiSubfamily_octic_superelliptic_of_omitted_shifted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    (T : MulChar F ℂ → Finset ℂ)
    (msteps e J D Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (gOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F[X])
    (ζOf : ∀ _ : MulChar F ℂ, F → F → F → ℂ → F)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (h8 : 8 ∣ (Fintype.card F - 1))
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
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ (Gchi χ), ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ Dset) :
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (((Gchi χ).card : ℝ) * M ^ 2) * (2 : ℕ)) := by
  have hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y :=
    chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero χ ψ G Dset Y homit
  exact approxB_away_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    ψ hψ χ G Dset hY T msteps e J D Dtot Cd gOf ζOf hmord hn hGD hCw0 hCmax2
    hYnonempty horder hres h8 hm hJ hT1 hT0 hvals hmodel hpoly he hmq hD
    hcount hDtot harith hCd0 hCdmax hq1 hnq hn4q hreg hdepth hM0 hM hs

end ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget

/-! ## Axiom audit -/
set_option linter.style.longLine false
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  incidence_le_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  approxB_away_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  incidence_le_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  approxB_away_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  chiSubfamilyResidualVanishesOff_of_omitted_twistedThinSum_zero
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  chiSubfamilyResidualVanishesOff_of_chiFamily_subset
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  chiSubfamilyResidualVanishesOff_self
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  incidence_le_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  approxB_away_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_omitted_shifted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_omitted_shifted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  incidence_le_of_chiSubfamily_octic_superelliptic_of_omitted_shifted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  approxB_away_of_chiSubfamily_octic_superelliptic_of_omitted_shifted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  incidence_le_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  approxB_away_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_shifted_zero
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  incidence_le_of_chiSubfamily_octic_superelliptic_of_shifted_zero
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  approxB_away_of_chiSubfamily_octic_superelliptic_of_shifted_zero
