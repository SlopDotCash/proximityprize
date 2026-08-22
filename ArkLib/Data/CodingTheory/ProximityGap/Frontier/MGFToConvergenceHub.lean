/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.SubexpMomentToConvergenceHub
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_layercake_moment

/-!
# From the S11 one-variable MGF residual to the convergence hub

`_wfS11_layercake_moment` proves the discrete layer-cake step:
a finite empirical MGF bound `MGFBound s t 1 c` yields the normalized moment envelope
`MomentEnvelope (fun r => (sum t_b^r) / |s|) 1 c`.

`SubexpMomentToConvergenceHub` then consumes such an envelope, provided the in-tree energy
`rEnergy G r` is dominated by `|G|^r` times that normalized moment. This file packages the
composition as the hub-facing S11 route with no explicit `MomentEnvelope` hypothesis.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


open AddChar
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ArkLib.ProximityGap.Frontier.WFS11
open ProximityGap.Frontier.SubexpMomentToConvergenceHub

namespace ProximityGap.Frontier.MGFToConvergenceHub

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The normalized empirical moments associated to a finite one-variable spectrum. -/
noncomputable def empiricalMoment {ι : Type*} (s : Finset ι) (t : ι → ℝ) (r : ℕ) : ℝ :=
  (∑ b ∈ s, (t b) ^ r) / (s.card : ℝ)

/-- The full-spectrum S11 normalized variable `t_b = ‖η_b‖² / |G|`. -/
noncomputable def fullSpectrumT (ψ : AddChar F ℂ) (G : Finset F) (b : F) : ℝ :=
  ‖eta ψ G b‖ ^ 2 / (G.card : ℝ)

/-- The full-spectrum normalized variable is nonnegative. -/
theorem fullSpectrumT_nonneg {ψ : AddChar F ℂ} {G : Finset F} (hGpos : 0 < G.card) :
    ∀ b ∈ (Finset.univ : Finset F), 0 ≤ fullSpectrumT ψ G b := by
  intro b _
  unfold fullSpectrumT
  exact div_nonneg (sq_nonneg _) (by positivity)

/-- For the full spectrum `t_b = ‖η_b‖² / |G|`, the empirical moments represent the in-tree
energy exactly, hence in particular dominate `rEnergy / |G|^r`. -/
theorem rEnergy_le_card_pow_mul_fullSpectrumMoment
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (hGpos : 0 < G.card)
    (r : ℕ) :
    (rEnergy G r : ℝ)
      ≤ (G.card : ℝ) ^ r
          * empiricalMoment (Finset.univ : Finset F) (fullSpectrumT ψ G) r := by
  classical
  have hG : 0 < (G.card : ℝ) := by exact_mod_cast hGpos
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < (G.card : ℝ) ^ r := pow_pos hG r
  have hsum := subgroup_gaussSum_moment hψ G r
  have hsumT :
      ∑ b : F, (fullSpectrumT ψ G b) ^ r
        = ((Fintype.card F : ℝ) * (rEnergy G r : ℝ)) / (G.card : ℝ) ^ r := by
    unfold fullSpectrumT
    calc
      ∑ b : F, (‖eta ψ G b‖ ^ 2 / (G.card : ℝ)) ^ r
          = ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) / (G.card : ℝ) ^ r := by
              refine Finset.sum_congr rfl (fun b _ => ?_)
              rw [div_pow, ← pow_mul]
      _ = (∑ b : F, ‖eta ψ G b‖ ^ (2 * r)) / (G.card : ℝ) ^ r := by
              rw [Finset.sum_div]
      _ = ((Fintype.card F : ℝ) * (rEnergy G r : ℝ)) / (G.card : ℝ) ^ r := by
              rw [hsum]
  rw [empiricalMoment]
  simp only [Finset.card_univ]
  rw [hsumT]
  exact le_of_eq (by field_simp [ne_of_gt hpow, ne_of_gt hq])

/-- A one-variable S11 MGF residual gives the spectral `NearRamanujanSqrtLog` face once the
empirical moments dominate the actual in-tree energies. -/
theorem nearRamanujan_of_mgf_depth_factor
    {ι : Type*} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (s : Finset ι) (t : ι → ℝ) {c C A : ℝ} {r : ℕ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hMGF : MGFBound s t 1 c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrA : (r : ℝ) ≤ A * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c) * A ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * empiricalMoment s t r) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_subexp_moment_depth_factor hψ G hc hc1 hC hGpos hq hr hrq hrA hconst
    (momentEnvelope_of_mgf s t hc ht hP hMGF)
    henergyRep

/-- A one-variable S11 MGF residual gives the convergence-hub `PrizeFloor` once the empirical
moments dominate the actual in-tree energies. -/
theorem prizeFloor_of_mgf_depth_factor
    {ι : Type*} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (s : Finset ι) (t : ι → ℝ) {c C A : ℝ} {r : ℕ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hMGF : MGFBound s t 1 c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrA : (r : ℝ) ≤ A * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c) * A ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * empiricalMoment s t r) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_subexp_moment_depth_factor hψ G hc hc1 hC hGpos hq hr hrq hrA hconst
    (momentEnvelope_of_mgf s t hc ht hP hMGF)
    henergyRep

/-- Full-spectrum MGF route to `NearRamanujanSqrtLog`: using
`t_b = ‖η_b‖² / |G|` over all additive frequencies, the energy-representation hypothesis is
discharged by the moment identity `∑_b ‖η_b‖^(2r) = q · rEnergy G r`. -/
theorem nearRamanujan_of_fullSpectrum_mgf_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {c C A : ℝ} {r : ℕ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C)
    (hMGF : MGFBound (Finset.univ : Finset F) (fullSpectrumT ψ G) 1 c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrA : (r : ℝ) ≤ A * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c) * A ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_mgf_depth_factor hψ G (Finset.univ : Finset F) (fullSpectrumT ψ G)
    hc hc1 hC (fullSpectrumT_nonneg hGpos) (by exact_mod_cast Fintype.card_pos)
    hMGF hGpos hq hr hrq hrA hconst
    (fun r _hr => rEnergy_le_card_pow_mul_fullSpectrumMoment hψ G hGpos r)

/-- Full-spectrum MGF route to the convergence-hub `PrizeFloor`: using
`t_b = ‖η_b‖² / |G|` over all additive frequencies, the energy-representation hypothesis is
discharged by the moment identity `∑_b ‖η_b‖^(2r) = q · rEnergy G r`. -/
theorem prizeFloor_of_fullSpectrum_mgf_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {c C A : ℝ} {r : ℕ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C)
    (hMGF : MGFBound (Finset.univ : Finset F) (fullSpectrumT ψ G) 1 c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrA : (r : ℝ) ≤ A * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c) * A ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_mgf_depth_factor hψ G (Finset.univ : Finset F) (fullSpectrumT ψ G)
    hc hc1 hC (fullSpectrumT_nonneg hGpos) (by exact_mod_cast Fintype.card_pos)
    hMGF hGpos hq hr hrq hrA hconst
    (fun r _hr => rEnergy_le_card_pow_mul_fullSpectrumMoment hψ G hGpos r)

end ProximityGap.Frontier.MGFToConvergenceHub

/-! ## Axiom audit -/
namespace ProximityGap.Frontier.MGFToConvergenceHub

#print axioms nearRamanujan_of_mgf_depth_factor
#print axioms prizeFloor_of_mgf_depth_factor
#print axioms rEnergy_le_card_pow_mul_fullSpectrumMoment
#print axioms nearRamanujan_of_fullSpectrum_mgf_depth_factor
#print axioms prizeFloor_of_fullSpectrum_mgf_depth_factor

end ProximityGap.Frontier.MGFToConvergenceHub
