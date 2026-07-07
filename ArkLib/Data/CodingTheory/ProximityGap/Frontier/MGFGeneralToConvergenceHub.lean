/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.MGFToConvergenceHub

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# General-constant MGF bounds into the convergence hub

`MGFToConvergenceHub` packages the sharp normalized case `MGFBound ... 1 c`.
Survival-tail and cutoff arguments more naturally produce `MGFBound ... A c` with `A ≥ 1`.
This file records the honest degradation: the S11 slack constant becomes `K = A / c`.
-/

open AddChar
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.WFS11
open ProximityGap.Frontier.EnergySlackToWraparoundK
open ProximityGap.Frontier.MGFToConvergenceHub

namespace ProximityGap.Frontier.MGFGeneralToConvergenceHub

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A general normalized moment envelope `M_r ≤ A r!/c^r` gives ordinary energy slack with
constant `K = A / c`, provided `A ≥ 1`. -/
theorem forall_rEnergy_le_mul_wick_of_momentEnvelope_general
    (G : Finset F) {M : ℕ → ℝ} {A c : ℝ}
    (hA : 1 ≤ A) (hc : 0 < c)
    (henv : MomentEnvelope M A c)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * M r) :
    ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ)
        ≤ (A / c) ^ r
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  intro r hr
  have hGnonneg : 0 ≤ (G.card : ℝ) := by positivity
  have hcardpow : 0 ≤ (G.card : ℝ) ^ r := pow_nonneg hGnonneg r
  have hAnonneg : 0 ≤ A := le_trans (by norm_num) hA
  have hcrpos : 0 < c ^ r := pow_pos hc r
  have henvr := henv r hr
  have hfac : (Nat.factorial r : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) :=
    factorial_le_doubleFactorial_odd r
  have hApow : A ≤ A ^ r := by
    simpa using pow_le_pow_right₀ hA hr
  calc
    (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * M r := henergyRep r hr
    _ ≤ (G.card : ℝ) ^ r * (A * (Nat.factorial r : ℝ) / c ^ r) := by
        exact mul_le_mul_of_nonneg_left henvr hcardpow
    _ ≤ (G.card : ℝ) ^ r * (A ^ r * (Nat.doubleFactorial (2 * r - 1) : ℝ) / c ^ r) := by
        apply mul_le_mul_of_nonneg_left
        · apply div_le_div_of_nonneg_right _ (le_of_lt hcrpos)
          calc
            A * (Nat.factorial r : ℝ)
                ≤ A * (Nat.doubleFactorial (2 * r - 1) : ℝ) := by
                  exact mul_le_mul_of_nonneg_left hfac hAnonneg
            _ ≤ A ^ r * (Nat.doubleFactorial (2 * r - 1) : ℝ) := by
                  exact mul_le_mul_of_nonneg_right hApow (by positivity)
        · exact hcardpow
    _ = (A / c) ^ r
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
        rw [div_pow]
        field_simp [ne_of_gt hcrpos]

/-- A general one-variable MGF bound gives the convergence-hub `PrizeFloor`, with the honest
slack constant `K = A / c`. -/
theorem prizeFloor_of_mgf_general_depth_factor
    {ι : Type*} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (s : Finset ι) (t : ι → ℝ) {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hMGF : MGFBound s t A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * empiricalMoment s t r) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_forall_rEnergy_le_mul_wick_depth_factor hψ G (by positivity) hC hGpos hq hr
    hrq hrK hconst
    (forall_rEnergy_le_mul_wick_of_momentEnvelope_general G hA hc
      (momentEnvelope_of_mgf s t hc ht hP hMGF) henergyRep)

/-- Full-spectrum general-MGF route to the convergence-hub `PrizeFloor`: using
`t_b = ‖η_b‖² / |G|` over all additive frequencies, the energy-representation hypothesis is
discharged by the moment identity from `MGFToConvergenceHub`. The honest slack constant is
`K = A / c`. -/
theorem prizeFloor_of_fullSpectrum_mgf_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (hMGF : MGFBound (Finset.univ : Finset F) (fullSpectrumT ψ G) A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_mgf_general_depth_factor hψ G
    (Finset.univ : Finset F) (fullSpectrumT ψ G) hA hc hC
    (fullSpectrumT_nonneg hGpos) (by exact_mod_cast Fintype.card_pos)
    hMGF hGpos hq hr hrq hrK hconst
    (fun r _hr => rEnergy_le_card_pow_mul_fullSpectrumMoment hψ G hGpos r)

end ProximityGap.Frontier.MGFGeneralToConvergenceHub

/-! ## Axiom audit -/
namespace ProximityGap.Frontier.MGFGeneralToConvergenceHub

#print axioms forall_rEnergy_le_mul_wick_of_momentEnvelope_general
#print axioms prizeFloor_of_mgf_general_depth_factor
#print axioms prizeFloor_of_fullSpectrum_mgf_general_depth_factor

end ProximityGap.Frontier.MGFGeneralToConvergenceHub
