/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.MGFToConvergenceHub
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_survival_to_mgf
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_mgf_rate_monotone

/-!
# General-constant MGF bounds into the convergence hub

`MGFToConvergenceHub` packages the sharp normalized case `MGFBound ... 1 c`.
Survival-tail and cutoff arguments more naturally produce `MGFBound ... A c` with `A ≥ 1`.
This file records the honest degradation: the S11 slack constant becomes `K = A / c`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


open AddChar
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ArkLib.ProximityGap.Frontier.WFS11
open ProximityGap.Frontier.EnergySlackToWraparoundK
open ProximityGap.Frontier.MGFToConvergenceHub
open ProximityGap.Frontier.WraparoundKToConvergenceHub

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

/-- A general one-variable MGF bound gives the spectral `NearRamanujanSqrtLog` face, with the
honest slack constant `K = A / c`. -/
theorem nearRamanujan_of_mgf_general_depth_factor
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
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_forall_q_wickExcess_le_mul_slack_core hψ G (by positivity) hC hr hrq
    (WraparoundKToConvergenceHub.prizeVariance_nonneg_of_card_le G hGpos hq)
    (core_scale_of_depth_le_log_mul G (by positivity)
      (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hGpos : (0 : ℝ) < (G.card : ℝ))).mpr
        (by simpa using hq)))
      hrK hconst)
    (forall_q_wickExcess_le_mul_slack_of_forall_rEnergy_le_mul_wick G
      (forall_rEnergy_le_mul_wick_of_momentEnvelope_general G hA hc
        (momentEnvelope_of_mgf s t hc ht hP hMGF) henergyRep))

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

/-- A general one-variable MGF bound at rate `c` gives the spectral `NearRamanujanSqrtLog`
face at any lower positive rate `c' ≤ c`, with the honest slack constant `K = A / c'`. -/
theorem nearRamanujan_of_mgf_rate_le_general_depth_factor
    {ι : Type*} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (s : Finset ι) (t : ι → ℝ) {A c c' C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hMGF : MGFBound s t A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c') * K ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * empiricalMoment s t r) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_mgf_general_depth_factor hψ G s t hA hc' hC ht hP
    (ArkLib.ProximityGap.Frontier.WFS11.MGFBound.of_rate_le s t ht hcc' hMGF)
    hGpos hq hr hrq hrK hconst henergyRep

/-- A general one-variable MGF bound at rate `c` gives the convergence-hub `PrizeFloor` at any
lower positive rate `c' ≤ c`, with the honest slack constant `K = A / c'`. -/
theorem prizeFloor_of_mgf_rate_le_general_depth_factor
    {ι : Type*} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (s : Finset ι) (t : ι → ℝ) {A c c' C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hMGF : MGFBound s t A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c') * K ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * empiricalMoment s t r) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_mgf_general_depth_factor hψ G s t hA hc' hC ht hP
    (ArkLib.ProximityGap.Frontier.WFS11.MGFBound.of_rate_le s t ht hcc' hMGF)
    hGpos hq hr hrq hrK hconst henergyRep

/-- Moment-envelope rate monotonicity: an envelope at rate `c` can be consumed at any lower
positive rate `c' ≤ c`. -/
theorem momentEnvelope_of_rate_le {M : ℕ → ℝ} {A c c' : ℝ}
    (hA : 0 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c)
    (henv : MomentEnvelope M A c) :
    MomentEnvelope M A c' := by
  intro r hr
  have hc : 0 < c := lt_of_lt_of_le hc' hcc'
  have hnum : 0 ≤ A * (Nat.factorial r : ℝ) := mul_nonneg hA (by positivity)
  exact (henv r hr).trans
    (div_le_div_of_nonneg_left hnum (pow_pos hc' r)
      (pow_le_pow_left₀ hc'.le hcc' r))

/-- A general normalized moment envelope gives the spectral `NearRamanujanSqrtLog` face directly,
without first packaging the envelope as an MGF certificate. This is the abstract S11 consumer for
any empirical spectrum whose moments dominate the normalized `rEnergy` terms. -/
theorem nearRamanujan_of_momentEnvelope_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℕ → ℝ} {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (henv : MomentEnvelope M A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * M r) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_forall_q_wickExcess_le_mul_slack_core hψ G (by positivity) hC hr hrq
    (WraparoundKToConvergenceHub.prizeVariance_nonneg_of_card_le G hGpos hq)
    (core_scale_of_depth_le_log_mul G (by positivity)
      (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hGpos : (0 : ℝ) < (G.card : ℝ))).mpr
        (by simpa using hq)))
      hrK hconst)
    (forall_q_wickExcess_le_mul_slack_of_forall_rEnergy_le_mul_wick G
      (forall_rEnergy_le_mul_wick_of_momentEnvelope_general G hA hc henv henergyRep))

/-- A general normalized moment envelope gives the convergence-hub `PrizeFloor` directly, with the
honest slack constant `K = A / c`. -/
theorem prizeFloor_of_momentEnvelope_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℕ → ℝ} {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (henv : MomentEnvelope M A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * M r) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_forall_rEnergy_le_mul_wick_depth_factor hψ G (by positivity) hC hGpos hq hr
    hrq hrK hconst
    (forall_rEnergy_le_mul_wick_of_momentEnvelope_general G hA hc henv henergyRep)

/-- A normalized moment envelope at rate `c` gives the spectral `NearRamanujanSqrtLog` face at
any lower positive rate `c' ≤ c`, with the honest slack constant `K = A / c'`. -/
theorem nearRamanujan_of_momentEnvelope_rate_le_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℕ → ℝ} {A c c' C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (henv : MomentEnvelope M A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c') * K ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * M r) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_momentEnvelope_general_depth_factor hψ G hA hc' hC
    (momentEnvelope_of_rate_le (le_trans (by norm_num) hA) hc' hcc' henv)
    hGpos hq hr hrq hrK hconst henergyRep

/-- A normalized moment envelope at rate `c` gives the convergence-hub `PrizeFloor` at any lower
positive rate `c' ≤ c`, with the honest slack constant `K = A / c'`. -/
theorem prizeFloor_of_momentEnvelope_rate_le_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℕ → ℝ} {A c c' C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (henv : MomentEnvelope M A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c') * K ≤ C ^ 2)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * M r) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_momentEnvelope_general_depth_factor hψ G hA hc' hC
    (momentEnvelope_of_rate_le (le_trans (by norm_num) hA) hc' hcc' henv)
    hGpos hq hr hrq hrK hconst henergyRep

/-- Full-spectrum general-MGF route to `NearRamanujanSqrtLog`: using
`t_b = ‖η_b‖² / |G|` over all additive frequencies, the energy-representation hypothesis is
discharged by the moment identity from `MGFToConvergenceHub`. The honest slack constant is
`K = A / c`. -/
theorem nearRamanujan_of_fullSpectrum_mgf_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (hMGF : MGFBound (Finset.univ : Finset F) (fullSpectrumT ψ G) A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_mgf_general_depth_factor hψ G
    (Finset.univ : Finset F) (fullSpectrumT ψ G) hA hc hC
    (fullSpectrumT_nonneg hGpos) (by exact_mod_cast Fintype.card_pos)
    hMGF hGpos hq hr hrq hrK hconst
    (fun r _hr => rEnergy_le_card_pow_mul_fullSpectrumMoment hψ G hGpos r)

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

/-- Full-spectrum moment-envelope route to the convergence-hub `PrizeFloor`. This is the direct
S11 consumer: if the empirical moments of
`t_b = ‖η_b‖² / |G|` obey `M_r ≤ A r! / c^r`, then the convergence hub gets the
honest slack constant `K = A / c`, with no intermediate MGF hypothesis. -/
theorem prizeFloor_of_fullSpectrum_momentEnvelope_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (henv : MomentEnvelope
      (empiricalMoment (Finset.univ : Finset F) (fullSpectrumT ψ G)) A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_forall_rEnergy_le_mul_wick_depth_factor hψ G (by positivity) hC hGpos hq hr
    hrq hrK hconst
    (forall_rEnergy_le_mul_wick_of_momentEnvelope_general G hA hc henv
      (fun r _hr => rEnergy_le_card_pow_mul_fullSpectrumMoment hψ G hGpos r))

/-- Full-spectrum moment-envelope route to `NearRamanujanSqrtLog`. This is the direct S11
consumer for the spectral face: if the empirical moments of `t_b = ‖η_b‖² / |G|` obey
`M_r ≤ A r! / c^r`, then the near-Ramanujan bound gets the honest slack constant `K = A / c`. -/
theorem nearRamanujan_of_fullSpectrum_momentEnvelope_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (henv : MomentEnvelope
      (empiricalMoment (Finset.univ : Finset F) (fullSpectrumT ψ G)) A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_forall_q_wickExcess_le_mul_slack_core hψ G (by positivity) hC hr hrq
    (WraparoundKToConvergenceHub.prizeVariance_nonneg_of_card_le G hGpos hq)
    (core_scale_of_depth_le_log_mul G (by positivity)
      (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hGpos : (0 : ℝ) < (G.card : ℝ))).mpr
        (by simpa using hq)))
      hrK hconst)
    (forall_q_wickExcess_le_mul_slack_of_forall_rEnergy_le_mul_wick G
      (forall_rEnergy_le_mul_wick_of_momentEnvelope_general G hA hc henv
        (fun r _hr => rEnergy_le_card_pow_mul_fullSpectrumMoment hψ G hGpos r)))

/-- Full-spectrum moment-envelope route to the convergence-hub `PrizeFloor`, with rate transfer:
an empirical moment envelope at rate `c` may be consumed at any lower positive rate `c' ≤ c`. -/
theorem prizeFloor_of_fullSpectrum_momentEnvelope_rate_le_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {A c c' C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (henv : MomentEnvelope
      (empiricalMoment (Finset.univ : Finset F) (fullSpectrumT ψ G)) A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c') * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_fullSpectrum_momentEnvelope_general_depth_factor hψ G hA hc' hC
    (momentEnvelope_of_rate_le (le_trans (by norm_num) hA) hc' hcc' henv)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum moment-envelope route to `NearRamanujanSqrtLog`, with rate transfer: an
empirical moment envelope at rate `c` may be consumed at any lower positive rate `c' ≤ c`. -/
theorem nearRamanujan_of_fullSpectrum_momentEnvelope_rate_le_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {A c c' C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (henv : MomentEnvelope
      (empiricalMoment (Finset.univ : Finset F) (fullSpectrumT ψ G)) A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c') * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_fullSpectrum_momentEnvelope_general_depth_factor hψ G hA hc' hC
    (momentEnvelope_of_rate_le (le_trans (by norm_num) hA) hc' hcc' henv)
    hGpos hq hr hrq hrK hconst

/-- A full-spectrum uniform cutoff `fullSpectrumT ψ G b ≤ T` gives the convergence-hub
`PrizeFloor`, with the honest cutoff slack constant `exp(c*T) / c`. -/
theorem nearRamanujan_of_fullSpectrum_cutoff_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {T c C K : ℝ} {r : ℕ}
    (hTnonneg : 0 ≤ T) (hc : 0 < c) (hC : 0 ≤ C)
    (hT : ∀ b ∈ (Finset.univ : Finset F), fullSpectrumT ψ G b ≤ T)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (Real.exp (c * T) / c) * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C := by
  have hA : 1 ≤ Real.exp (c * T) := by
    simpa [Real.one_le_exp_iff] using mul_nonneg hc.le hTnonneg
  exact nearRamanujan_of_fullSpectrum_mgf_general_depth_factor hψ G hA hc hC
    (mgfBound_of_max_ceiling (Finset.univ : Finset F) (fullSpectrumT ψ G) hc.le hT)
    hGpos hq hr hrq hrK hconst

/-- A full-spectrum uniform cutoff `fullSpectrumT ψ G b ≤ T` gives the convergence-hub
`PrizeFloor`, with the honest cutoff slack constant `exp(c*T) / c`. -/
theorem prizeFloor_of_fullSpectrum_cutoff_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {T c C K : ℝ} {r : ℕ}
    (hTnonneg : 0 ≤ T) (hc : 0 < c) (hC : 0 ≤ C)
    (hT : ∀ b ∈ (Finset.univ : Finset F), fullSpectrumT ψ G b ≤ T)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (Real.exp (c * T) / c) * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C := by
  have hA : 1 ≤ Real.exp (c * T) := by
    simpa [Real.one_le_exp_iff] using mul_nonneg hc.le hTnonneg
  exact prizeFloor_of_fullSpectrum_mgf_general_depth_factor hψ G hA hc hC
    (mgfBound_of_max_ceiling (Finset.univ : Finset F) (fullSpectrumT ψ G) hc.le hT)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum uniform cutoff route to `NearRamanujanSqrtLog`, deriving the cutoff
nonnegativity from the nonnegative spectrum itself. -/
theorem nearRamanujan_of_fullSpectrum_cutoff_depth_factor_auto_nonneg
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {T c C K : ℝ} {r : ℕ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hT : ∀ b ∈ (Finset.univ : Finset F), fullSpectrumT ψ G b ≤ T)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (Real.exp (c * T) / c) * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_fullSpectrum_cutoff_depth_factor hψ G
    ((fullSpectrumT_nonneg (ψ := ψ) (G := G) hGpos 0 (Finset.mem_univ 0)).trans
      (hT 0 (Finset.mem_univ 0)))
    hc hC hT hGpos hq hr hrq hrK hconst

/-- Full-spectrum uniform cutoff route to `PrizeFloor`, deriving the cutoff nonnegativity from
the nonnegative spectrum itself. -/
theorem prizeFloor_of_fullSpectrum_cutoff_depth_factor_auto_nonneg
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {T c C K : ℝ} {r : ℕ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hT : ∀ b ∈ (Finset.univ : Finset F), fullSpectrumT ψ G b ≤ T)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (Real.exp (c * T) / c) * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_fullSpectrum_cutoff_depth_factor hψ G
    ((fullSpectrumT_nonneg (ψ := ψ) (G := G) hGpos 0 (Finset.mem_univ 0)).trans
      (hT 0 (Finset.mem_univ 0)))
    hc hC hT hGpos hq hr hrq hrK hconst

/-- Full-spectrum higher-rate MGF route to `NearRamanujanSqrtLog`: a certificate at rate `c`
can be consumed at any lower positive rate `c' ≤ c`, with the honest slack constant `A / c'`. -/
theorem nearRamanujan_of_fullSpectrum_mgf_rate_le_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {A c c' C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (hMGF : MGFBound (Finset.univ : Finset F) (fullSpectrumT ψ G) A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c') * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_fullSpectrum_mgf_general_depth_factor hψ G hA hc' hC
    (ArkLib.ProximityGap.Frontier.WFS11.MGFBound.of_rate_le
      (Finset.univ : Finset F) (fullSpectrumT ψ G) (fullSpectrumT_nonneg hGpos) hcc' hMGF)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum higher-rate MGF route to the convergence-hub `PrizeFloor`: a certificate at
rate `c` can be consumed at any lower positive rate `c' ≤ c`, with slack constant `A / c'`. -/
theorem prizeFloor_of_fullSpectrum_mgf_rate_le_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {A c c' C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (hMGF : MGFBound (Finset.univ : Finset F) (fullSpectrumT ψ G) A c)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c') * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_fullSpectrum_mgf_general_depth_factor hψ G hA hc' hC
    (ArkLib.ProximityGap.Frontier.WFS11.MGFBound.of_rate_le
      (Finset.univ : Finset F) (fullSpectrumT ψ G) (fullSpectrumT_nonneg hGpos) hcc' hMGF)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum uniform cutoff route to `NearRamanujanSqrtLog`, with rate transfer: a cutoff
MGF certificate at rate `c` may be consumed at any lower positive rate `c' ≤ c`. -/
theorem nearRamanujan_of_fullSpectrum_cutoff_rate_le_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {T c c' C K : ℝ} {r : ℕ}
    (hTnonneg : 0 ≤ T) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (hT : ∀ b ∈ (Finset.univ : Finset F), fullSpectrumT ψ G b ≤ T)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (Real.exp (c * T) / c') * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C := by
  have hc : 0 < c := lt_of_lt_of_le hc' hcc'
  have hA : 1 ≤ Real.exp (c * T) := by
    simpa [Real.one_le_exp_iff] using mul_nonneg hc.le hTnonneg
  exact nearRamanujan_of_fullSpectrum_mgf_rate_le_general_depth_factor hψ G hA hc'
    hcc' hC
    (mgfBound_of_max_ceiling (Finset.univ : Finset F) (fullSpectrumT ψ G) hc.le hT)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum uniform cutoff route to `PrizeFloor`, with rate transfer: a cutoff MGF
certificate at rate `c` may be consumed at any lower positive rate `c' ≤ c`. -/
theorem prizeFloor_of_fullSpectrum_cutoff_rate_le_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {T c c' C K : ℝ} {r : ℕ}
    (hTnonneg : 0 ≤ T) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (hT : ∀ b ∈ (Finset.univ : Finset F), fullSpectrumT ψ G b ≤ T)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (Real.exp (c * T) / c') * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C := by
  have hc : 0 < c := lt_of_lt_of_le hc' hcc'
  have hA : 1 ≤ Real.exp (c * T) := by
    simpa [Real.one_le_exp_iff] using mul_nonneg hc.le hTnonneg
  exact prizeFloor_of_fullSpectrum_mgf_rate_le_general_depth_factor hψ G hA hc'
    hcc' hC
    (mgfBound_of_max_ceiling (Finset.univ : Finset F) (fullSpectrumT ψ G) hc.le hT)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum uniform cutoff route to `NearRamanujanSqrtLog`, with rate transfer and automatic
cutoff nonnegativity from the spectrum. -/
theorem nearRamanujan_of_fullSpectrum_cutoff_rate_le_depth_factor_auto_nonneg
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {T c c' C K : ℝ} {r : ℕ}
    (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (hT : ∀ b ∈ (Finset.univ : Finset F), fullSpectrumT ψ G b ≤ T)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (Real.exp (c * T) / c') * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_fullSpectrum_cutoff_rate_le_depth_factor hψ G
    ((fullSpectrumT_nonneg (ψ := ψ) (G := G) hGpos 0 (Finset.mem_univ 0)).trans
      (hT 0 (Finset.mem_univ 0)))
    hc' hcc' hC hT hGpos hq hr hrq hrK hconst

/-- Full-spectrum uniform cutoff route to `PrizeFloor`, with rate transfer and automatic cutoff
nonnegativity from the spectrum. -/
theorem prizeFloor_of_fullSpectrum_cutoff_rate_le_depth_factor_auto_nonneg
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {T c c' C K : ℝ} {r : ℕ}
    (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (hT : ∀ b ∈ (Finset.univ : Finset F), fullSpectrumT ψ G b ≤ T)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (Real.exp (c * T) / c') * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_fullSpectrum_cutoff_rate_le_depth_factor hψ G
    ((fullSpectrumT_nonneg (ψ := ψ) (G := G) hGpos 0 (Finset.mem_univ 0)).trans
      (hT 0 (Finset.mem_univ 0)))
    hc' hcc' hC hT hGpos hq hr hrq hrK hconst

/-- Full-spectrum survival-count route to `NearRamanujanSqrtLog`: a threshold-grid staircase
dominating the exponential weights, together with explicit survival-count ceilings, gives the
full-spectrum `MGFBound` and hence the spectral face. -/
theorem nearRamanujan_of_fullSpectrum_survival_count_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (Θ : Finset ℝ) (δ B : ℝ → ℝ) {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ (Finset.univ : Finset F),
      Real.exp (c * fullSpectrumT ψ G b) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ fullSpectrumT ψ G b), δ θ)
    (hcount : ∀ θ ∈ Θ,
      (((Finset.univ : Finset F).filter (fun b => θ ≤ fullSpectrumT ψ G b)).card : ℝ) ≤ B θ)
    (hweighted : (∑ θ ∈ Θ, δ θ * B θ) ≤ A * ((Finset.univ : Finset F).card : ℝ))
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_fullSpectrum_mgf_general_depth_factor hψ G hA hc hC
    (mgfBound_of_survival_count_ceiling (Finset.univ : Finset F)
      (fullSpectrumT ψ G) Θ δ B hδ hstair hcount hweighted)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum survival-count route to the convergence-hub `PrizeFloor`: a threshold-grid
survival-count certificate gives the full-spectrum `MGFBound` and hence the hub. -/
theorem prizeFloor_of_fullSpectrum_survival_count_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (Θ : Finset ℝ) (δ B : ℝ → ℝ) {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ (Finset.univ : Finset F),
      Real.exp (c * fullSpectrumT ψ G b) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ fullSpectrumT ψ G b), δ θ)
    (hcount : ∀ θ ∈ Θ,
      (((Finset.univ : Finset F).filter (fun b => θ ≤ fullSpectrumT ψ G b)).card : ℝ) ≤ B θ)
    (hweighted : (∑ θ ∈ Θ, δ θ * B θ) ≤ A * ((Finset.univ : Finset F).card : ℝ))
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_fullSpectrum_mgf_general_depth_factor hψ G hA hc hC
    (mgfBound_of_survival_count_ceiling (Finset.univ : Finset F)
      (fullSpectrumT ψ G) Θ δ B hδ hstair hcount hweighted)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum weighted-survival route to `NearRamanujanSqrtLog`: if the staircase domination
has already been summed against the *actual* survival counts, it can be consumed directly without
introducing a separate numerical ceiling function `B`. -/
theorem nearRamanujan_of_fullSpectrum_survival_weighted_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ (Finset.univ : Finset F),
      Real.exp (c * fullSpectrumT ψ G b) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ fullSpectrumT ψ G b), δ θ)
    (hweighted :
      (∑ θ ∈ Θ,
        δ θ *
          (((Finset.univ : Finset F).filter (fun b => θ ≤ fullSpectrumT ψ G b)).card : ℝ))
        ≤ A * ((Finset.univ : Finset F).card : ℝ))
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_fullSpectrum_mgf_general_depth_factor hψ G hA hc hC
    (mgfBound_of_survival_weighted_ceiling (Finset.univ : Finset F)
      (fullSpectrumT ψ G) Θ δ hδ hstair hweighted)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum weighted-survival route to the convergence-hub `PrizeFloor`: the exact
survival-weighted layer-cake sum can be consumed directly as a general `MGFBound` certificate. -/
theorem prizeFloor_of_fullSpectrum_survival_weighted_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ (Finset.univ : Finset F),
      Real.exp (c * fullSpectrumT ψ G b) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ fullSpectrumT ψ G b), δ θ)
    (hweighted :
      (∑ θ ∈ Θ,
        δ θ *
          (((Finset.univ : Finset F).filter (fun b => θ ≤ fullSpectrumT ψ G b)).card : ℝ))
        ≤ A * ((Finset.univ : Finset F).card : ℝ))
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_fullSpectrum_mgf_general_depth_factor hψ G hA hc hC
    (mgfBound_of_survival_weighted_ceiling (Finset.univ : Finset F)
      (fullSpectrumT ψ G) Θ δ hδ hstair hweighted)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum survival-count route to `NearRamanujanSqrtLog`, with rate transfer: a
certificate at exponential rate `c` may be consumed at any lower positive rate `c' ≤ c`. -/
theorem nearRamanujan_of_fullSpectrum_survival_count_rate_le_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (Θ : Finset ℝ) (δ B : ℝ → ℝ) {A c c' C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ (Finset.univ : Finset F),
      Real.exp (c * fullSpectrumT ψ G b) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ fullSpectrumT ψ G b), δ θ)
    (hcount : ∀ θ ∈ Θ,
      (((Finset.univ : Finset F).filter (fun b => θ ≤ fullSpectrumT ψ G b)).card : ℝ) ≤ B θ)
    (hweighted : (∑ θ ∈ Θ, δ θ * B θ) ≤ A * ((Finset.univ : Finset F).card : ℝ))
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c') * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_fullSpectrum_mgf_rate_le_general_depth_factor hψ G hA hc' hcc' hC
    (mgfBound_of_survival_count_ceiling (Finset.univ : Finset F)
      (fullSpectrumT ψ G) Θ δ B hδ hstair hcount hweighted)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum survival-count route to the convergence-hub `PrizeFloor`, with rate transfer:
a certificate at exponential rate `c` may be consumed at any lower positive rate `c' ≤ c`. -/
theorem prizeFloor_of_fullSpectrum_survival_count_rate_le_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (Θ : Finset ℝ) (δ B : ℝ → ℝ) {A c c' C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ (Finset.univ : Finset F),
      Real.exp (c * fullSpectrumT ψ G b) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ fullSpectrumT ψ G b), δ θ)
    (hcount : ∀ θ ∈ Θ,
      (((Finset.univ : Finset F).filter (fun b => θ ≤ fullSpectrumT ψ G b)).card : ℝ) ≤ B θ)
    (hweighted : (∑ θ ∈ Θ, δ θ * B θ) ≤ A * ((Finset.univ : Finset F).card : ℝ))
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c') * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_fullSpectrum_mgf_rate_le_general_depth_factor hψ G hA hc' hcc' hC
    (mgfBound_of_survival_count_ceiling (Finset.univ : Finset F)
      (fullSpectrumT ψ G) Θ δ B hδ hstair hcount hweighted)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum weighted-survival route to `NearRamanujanSqrtLog`, with rate transfer: if the
actual survival-weighted staircase certifies the MGF at rate `c`, it can be consumed at any lower
positive rate `c' ≤ c`. -/
theorem nearRamanujan_of_fullSpectrum_survival_weighted_rate_le_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) {A c c' C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ (Finset.univ : Finset F),
      Real.exp (c * fullSpectrumT ψ G b) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ fullSpectrumT ψ G b), δ θ)
    (hweighted :
      (∑ θ ∈ Θ,
        δ θ *
          (((Finset.univ : Finset F).filter (fun b => θ ≤ fullSpectrumT ψ G b)).card : ℝ))
        ≤ A * ((Finset.univ : Finset F).card : ℝ))
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c') * K ≤ C ^ 2) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_fullSpectrum_mgf_rate_le_general_depth_factor hψ G hA hc' hcc' hC
    (mgfBound_of_survival_weighted_ceiling (Finset.univ : Finset F)
      (fullSpectrumT ψ G) Θ δ hδ hstair hweighted)
    hGpos hq hr hrq hrK hconst

/-- Full-spectrum weighted-survival route to the convergence-hub `PrizeFloor`, with rate transfer:
if the actual survival-weighted staircase certifies the MGF at rate `c`, it can be consumed at any
lower positive rate `c' ≤ c`. -/
theorem prizeFloor_of_fullSpectrum_survival_weighted_rate_le_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) {A c c' C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc' : 0 < c') (hcc' : c' ≤ c) (hC : 0 ≤ C)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ (Finset.univ : Finset F),
      Real.exp (c * fullSpectrumT ψ G b) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ fullSpectrumT ψ G b), δ θ)
    (hweighted :
      (∑ θ ∈ Θ,
        δ θ *
          (((Finset.univ : Finset F).filter (fun b => θ ≤ fullSpectrumT ψ G b)).card : ℝ))
        ≤ A * ((Finset.univ : Finset F).card : ℝ))
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c') * K ≤ C ^ 2) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_fullSpectrum_mgf_rate_le_general_depth_factor hψ G hA hc' hcc' hC
    (mgfBound_of_survival_weighted_ceiling (Finset.univ : Finset F)
      (fullSpectrumT ψ G) Θ δ hδ hstair hweighted)
    hGpos hq hr hrq hrK hconst

end ProximityGap.Frontier.MGFGeneralToConvergenceHub

/-! ## Axiom audit -/
namespace ProximityGap.Frontier.MGFGeneralToConvergenceHub

#print axioms forall_rEnergy_le_mul_wick_of_momentEnvelope_general
#print axioms nearRamanujan_of_mgf_general_depth_factor
#print axioms prizeFloor_of_mgf_general_depth_factor
#print axioms nearRamanujan_of_mgf_rate_le_general_depth_factor
#print axioms prizeFloor_of_mgf_rate_le_general_depth_factor
#print axioms momentEnvelope_of_rate_le
#print axioms nearRamanujan_of_momentEnvelope_general_depth_factor
#print axioms prizeFloor_of_momentEnvelope_general_depth_factor
#print axioms nearRamanujan_of_momentEnvelope_rate_le_general_depth_factor
#print axioms prizeFloor_of_momentEnvelope_rate_le_general_depth_factor
#print axioms nearRamanujan_of_fullSpectrum_mgf_general_depth_factor
#print axioms prizeFloor_of_fullSpectrum_mgf_general_depth_factor
#print axioms nearRamanujan_of_fullSpectrum_momentEnvelope_general_depth_factor
#print axioms prizeFloor_of_fullSpectrum_momentEnvelope_general_depth_factor
#print axioms nearRamanujan_of_fullSpectrum_momentEnvelope_rate_le_general_depth_factor
#print axioms prizeFloor_of_fullSpectrum_momentEnvelope_rate_le_general_depth_factor
#print axioms nearRamanujan_of_fullSpectrum_cutoff_depth_factor
#print axioms prizeFloor_of_fullSpectrum_cutoff_depth_factor
#print axioms nearRamanujan_of_fullSpectrum_cutoff_depth_factor_auto_nonneg
#print axioms prizeFloor_of_fullSpectrum_cutoff_depth_factor_auto_nonneg
#print axioms nearRamanujan_of_fullSpectrum_mgf_rate_le_general_depth_factor
#print axioms prizeFloor_of_fullSpectrum_mgf_rate_le_general_depth_factor
#print axioms nearRamanujan_of_fullSpectrum_cutoff_rate_le_depth_factor
#print axioms prizeFloor_of_fullSpectrum_cutoff_rate_le_depth_factor
#print axioms nearRamanujan_of_fullSpectrum_cutoff_rate_le_depth_factor_auto_nonneg
#print axioms prizeFloor_of_fullSpectrum_cutoff_rate_le_depth_factor_auto_nonneg
#print axioms nearRamanujan_of_fullSpectrum_survival_count_general_depth_factor
#print axioms prizeFloor_of_fullSpectrum_survival_count_general_depth_factor
#print axioms nearRamanujan_of_fullSpectrum_survival_weighted_general_depth_factor
#print axioms prizeFloor_of_fullSpectrum_survival_weighted_general_depth_factor
#print axioms nearRamanujan_of_fullSpectrum_survival_count_rate_le_general_depth_factor
#print axioms prizeFloor_of_fullSpectrum_survival_count_rate_le_general_depth_factor
#print axioms nearRamanujan_of_fullSpectrum_survival_weighted_rate_le_general_depth_factor
#print axioms prizeFloor_of_fullSpectrum_survival_weighted_rate_le_general_depth_factor

end ProximityGap.Frontier.MGFGeneralToConvergenceHub
