/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.MGFGeneralToConvergenceHub

/-!
# Small-MGF adapters into the convergence hub

`MGFToConvergenceHub` consumes the normalized S11 residual `MGFBound s t 1 c`.  Some upstream
concentration statements naturally produce the stronger form `MGFBound s t A c` with `A ≤ 1`.
This file packages the monotone coercion and the corresponding hub consumers.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open AddChar
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ArkLib.ProximityGap.Frontier.WFS11
open ProximityGap.Frontier.MGFToConvergenceHub
open ProximityGap.Frontier.MGFGeneralToConvergenceHub

namespace ProximityGap.Frontier.R149MGFSmallToConvergenceHub

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A subunit empirical MGF certificate is, in particular, the normalized `A = 1` certificate
consumed by the S11 convergence-hub route. -/
theorem mgfBound_one_of_le_one {ι : Type*} (s : Finset ι) (t : ι → ℝ) {A c : ℝ}
    (hA : A ≤ 1) (hMGF : MGFBound s t A c) :
    MGFBound s t 1 c := by
  unfold MGFBound at hMGF ⊢
  exact hMGF.trans (mul_le_mul_of_nonneg_right hA (by positivity))

/-- A stronger one-variable S11 MGF residual `A ≤ 1` gives the spectral
`NearRamanujanSqrtLog` face once the empirical moments dominate the actual in-tree energies. -/
theorem nearRamanujan_of_mgf_le_one_depth_factor
    {ι : Type*} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (s : Finset ι) (t : ι → ℝ) {A c C K : ℝ} {r : ℕ}
    (hA : A ≤ 1) (hc : 0 < c) (hC : 0 ≤ C)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hMGF : MGFBound s t A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c) * K ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * empiricalMoment s t r) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_mgf_general_depth_factor hψ G s t (by norm_num) hc hC ht hP
    (mgfBound_one_of_le_one s t hA hMGF) hGpos hq hr hrq hrK hconst henergyRep

/-- A stronger one-variable S11 MGF residual `A ≤ 1` gives the convergence-hub `PrizeFloor`
once the empirical moments dominate the actual in-tree energies. -/
theorem prizeFloor_of_mgf_le_one_depth_factor
    {ι : Type*} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (s : Finset ι) (t : ι → ℝ) {A c C K : ℝ} {r : ℕ}
    (hA : A ≤ 1) (hc : 0 < c) (hC : 0 ≤ C)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hMGF : MGFBound s t A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c) * K ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * empiricalMoment s t r) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_mgf_general_depth_factor hψ G s t (by norm_num) hc hC ht hP
    (mgfBound_one_of_le_one s t hA hMGF) hGpos hq hr hrq hrK hconst henergyRep

/-- A stronger one-variable S11 MGF residual `A ≤ 1` at rate `c` gives the spectral
`NearRamanujanSqrtLog` face at any lower positive rate `c' ≤ c`. -/
theorem nearRamanujan_of_mgf_le_one_rate_le_depth_factor
    {ι : Type*} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (s : Finset ι) (t : ι → ℝ) {A c c' C K : ℝ} {r : ℕ}
    (hA : A ≤ 1) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hMGF : MGFBound s t A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c') * K ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * empiricalMoment s t r) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_mgf_rate_le_general_depth_factor hψ G s t (by norm_num) hc' hcc' hC ht hP
    (mgfBound_one_of_le_one s t hA hMGF) hGpos hq hr hrq hrK hconst henergyRep

/-- A stronger one-variable S11 MGF residual `A ≤ 1` at rate `c` gives the convergence-hub
`PrizeFloor` at any lower positive rate `c' ≤ c`. -/
theorem prizeFloor_of_mgf_le_one_rate_le_depth_factor
    {ι : Type*} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (s : Finset ι) (t : ι → ℝ) {A c c' C K : ℝ} {r : ℕ}
    (hA : A ≤ 1) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hMGF : MGFBound s t A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c') * K ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * empiricalMoment s t r) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_mgf_rate_le_general_depth_factor hψ G s t (by norm_num) hc' hcc' hC ht hP
    (mgfBound_one_of_le_one s t hA hMGF) hGpos hq hr hrq hrK hconst henergyRep

/-- Full-spectrum version of `nearRamanujan_of_mgf_le_one_depth_factor`: for
`t_b = ‖η_b‖² / |G|` over all additive frequencies, the energy-representation hypothesis is
discharged by `MGFToConvergenceHub`. -/
theorem nearRamanujan_of_fullSpectrum_mgf_le_one_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {A c C K : ℝ} {r : ℕ}
    (hA : A ≤ 1) (hc : 0 < c) (hC : 0 ≤ C)
    (hMGF : MGFBound (Finset.univ : Finset F) (fullSpectrumT ψ G) A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c) * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_fullSpectrum_mgf_general_depth_factor hψ G (by norm_num) hc hC
    (mgfBound_one_of_le_one (Finset.univ : Finset F) (fullSpectrumT ψ G) hA hMGF)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum version of `prizeFloor_of_mgf_le_one_depth_factor`: for
`t_b = ‖η_b‖² / |G|` over all additive frequencies, the energy-representation hypothesis is
discharged by `MGFToConvergenceHub`. -/
theorem prizeFloor_of_fullSpectrum_mgf_le_one_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {A c C K : ℝ} {r : ℕ}
    (hA : A ≤ 1) (hc : 0 < c) (hC : 0 ≤ C)
    (hMGF : MGFBound (Finset.univ : Finset F) (fullSpectrumT ψ G) A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c) * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_fullSpectrum_mgf_general_depth_factor hψ G (by norm_num) hc hC
    (mgfBound_one_of_le_one (Finset.univ : Finset F) (fullSpectrumT ψ G) hA hMGF)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum version of `nearRamanujan_of_mgf_le_one_rate_le_depth_factor`: a subunit MGF
certificate at rate `c` can be consumed at any lower positive rate `c' ≤ c`. -/
theorem nearRamanujan_of_fullSpectrum_mgf_le_one_rate_le_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {A c c' C K : ℝ} {r : ℕ}
    (hA : A ≤ 1) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (hMGF : MGFBound (Finset.univ : Finset F) (fullSpectrumT ψ G) A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c') * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_fullSpectrum_mgf_rate_le_general_depth_factor hψ G
    (by norm_num) hc' hcc' hC
    (mgfBound_one_of_le_one (Finset.univ : Finset F) (fullSpectrumT ψ G) hA hMGF)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum version of `prizeFloor_of_mgf_le_one_rate_le_depth_factor`: a subunit MGF
certificate at rate `c` can be consumed by the hub at any lower positive rate `c' ≤ c`. -/
theorem prizeFloor_of_fullSpectrum_mgf_le_one_rate_le_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {A c c' C K : ℝ} {r : ℕ}
    (hA : A ≤ 1) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (hMGF : MGFBound (Finset.univ : Finset F) (fullSpectrumT ψ G) A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c') * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_fullSpectrum_mgf_rate_le_general_depth_factor hψ G
    (by norm_num) hc' hcc' hC
    (mgfBound_one_of_le_one (Finset.univ : Finset F) (fullSpectrumT ψ G) hA hMGF)
    hGpos hq hr hrq hrK hconst

end ProximityGap.Frontier.R149MGFSmallToConvergenceHub

/-! ## Axiom audit -/
namespace ProximityGap.Frontier.R149MGFSmallToConvergenceHub

#print axioms mgfBound_one_of_le_one
#print axioms nearRamanujan_of_mgf_le_one_depth_factor
#print axioms prizeFloor_of_mgf_le_one_depth_factor
#print axioms nearRamanujan_of_mgf_le_one_rate_le_depth_factor
#print axioms prizeFloor_of_mgf_le_one_rate_le_depth_factor
#print axioms nearRamanujan_of_fullSpectrum_mgf_le_one_depth_factor
#print axioms prizeFloor_of_fullSpectrum_mgf_le_one_depth_factor
#print axioms nearRamanujan_of_fullSpectrum_mgf_le_one_rate_le_depth_factor
#print axioms prizeFloor_of_fullSpectrum_mgf_le_one_rate_le_depth_factor

end ProximityGap.Frontier.R149MGFSmallToConvergenceHub
