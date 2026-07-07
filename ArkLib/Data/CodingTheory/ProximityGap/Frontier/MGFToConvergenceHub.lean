/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.SubexpMomentToConvergenceHub
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_layercake_moment

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# From the S11 one-variable MGF residual to the convergence hub

`_wfS11_layercake_moment` proves the discrete layer-cake step:
a finite empirical MGF bound `MGFBound s t 1 c` yields the normalized moment envelope
`MomentEnvelope (fun r => (sum t_b^r) / |s|) 1 c`.

`SubexpMomentToConvergenceHub` then consumes such an envelope, provided the in-tree energy
`rEnergy G r` is dominated by `|G|^r` times that normalized moment. This file packages the
composition as the hub-facing S11 route with no explicit `MomentEnvelope` hypothesis.
-/

open AddChar
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ArkLib.ProximityGap.Frontier.WFS11
open ProximityGap.Frontier.SubexpMomentToConvergenceHub

namespace ProximityGap.Frontier.MGFToConvergenceHub

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The normalized empirical moments associated to a finite one-variable spectrum. -/
noncomputable def empiricalMoment {ι : Type*} (s : Finset ι) (t : ι → ℝ) (r : ℕ) : ℝ :=
  (∑ b ∈ s, (t b) ^ r) / (s.card : ℝ)

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

end ProximityGap.Frontier.MGFToConvergenceHub

/-! ## Axiom audit -/
namespace ProximityGap.Frontier.MGFToConvergenceHub

#print axioms nearRamanujan_of_mgf_depth_factor
#print axioms prizeFloor_of_mgf_depth_factor

end ProximityGap.Frontier.MGFToConvergenceHub
