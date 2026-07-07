/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.EnergySlackToWraparoundK
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_subexp_tail_to_slack

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# From the S11 sub-exponential moment envelope to the convergence hub

`_wfS11_subexp_tail_to_slack` proves that a normalized sub-exponential moment envelope
`MomentEnvelope M 1 c` gives an S1 energy slack with `K = 1 / c`, for an abstract normalized moment
functional `M`.

This file adds the final hub-facing packaging: once the actual in-tree energy `rEnergy G r` is
dominated by `|G|^r * M r`, the S11 envelope feeds the ordinary energy-slack adapter and lands in
`ConvergenceHub.PrizeFloor`.
-/

open AddChar
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ArkLib.ProximityGap.Frontier.WFS11
open ProximityGap.Frontier.EnergySlackToWraparoundK
open ProximityGap.Frontier.WraparoundKToConvergenceHub

namespace ProximityGap.Frontier.SubexpMomentToConvergenceHub

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A general S11 moment envelope gives the multiplicative energy slack for the actual in-tree
energy, provided the normalized moment functional dominates `rEnergy / |G|^r`. The honest slack
constant is `K = A / c`. -/
theorem forall_rEnergy_le_mul_wick_of_subexp_moment_general
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

/-- General S11 hub-facing consumer: a sub-exponential moment envelope with constant `A` lands in
the spectral `NearRamanujanSqrtLog` face after the usual depth/constant bookkeeping. -/
theorem nearRamanujan_of_subexp_moment_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℕ → ℝ} {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2)
    (henv : MomentEnvelope M A c)
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
      (forall_rEnergy_le_mul_wick_of_subexp_moment_general G hA hc henv henergyRep))

/-- General S11 hub-facing consumer: a sub-exponential moment envelope with constant `A` lands in
`PrizeFloor`, with the honest slack constant `K = A / c`. -/
theorem prizeFloor_of_subexp_moment_general_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℕ → ℝ} {A c C K : ℝ} {r : ℕ}
    (hA : 1 ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrK : (r : ℝ) ≤ K * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (A / c) * K ≤ C ^ 2)
    (henv : MomentEnvelope M A c)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * M r) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_forall_rEnergy_le_mul_wick_depth_factor hψ G (by positivity) hC hGpos hq hr
    hrq hrK hconst
    (forall_rEnergy_le_mul_wick_of_subexp_moment_general G hA hc henv henergyRep)

/-- A normalized S11 moment envelope gives the multiplicative energy slack for the actual in-tree
energy, provided the normalized moment functional dominates `rEnergy / |G|^r`. -/
theorem forall_rEnergy_le_mul_wick_of_subexp_moment
    (G : Finset F) {M : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1)
    (henv : MomentEnvelope M 1 c)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * M r) :
    ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ)
        ≤ (1 / c) ^ r
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  intro r hr
  have hn : 0 ≤ (G.card : ℝ) := by positivity
  have hslack :=
    slack_of_subexp_moment (M := M) (n := (G.card : ℝ)) hn hc hc1 henv r hr
  calc
    (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * M r := henergyRep r hr
    _ ≤ (1 / c) ^ r * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r :=
        hslack
    _ = (1 / c) ^ r
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by ring

/-- S11 hub-facing consumer: a normalized sub-exponential moment envelope, plus the usual
normalization domination for `rEnergy`, lands in the spectral `NearRamanujanSqrtLog` face after
the depth/constant bookkeeping. -/
theorem nearRamanujan_of_subexp_moment_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℕ → ℝ} {c C A : ℝ} {r : ℕ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrA : (r : ℝ) ≤ A * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c) * A ≤ C ^ 2)
    (henv : MomentEnvelope M 1 c)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * M r) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_forall_q_wickExcess_le_mul_slack_core hψ G (by positivity) hC hr hrq
    (WraparoundKToConvergenceHub.prizeVariance_nonneg_of_card_le G hGpos hq)
    (core_scale_of_depth_le_log_mul G (by positivity)
      (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hGpos : (0 : ℝ) < (G.card : ℝ))).mpr
        (by simpa using hq)))
      hrA hconst)
    (forall_q_wickExcess_le_mul_slack_of_forall_rEnergy_le_mul_wick G
      (forall_rEnergy_le_mul_wick_of_subexp_moment G hc hc1 henv henergyRep))

/-- S11 hub-facing consumer: a normalized sub-exponential moment envelope, plus the usual
normalization domination for `rEnergy`, lands in `PrizeFloor` after the depth/constant
bookkeeping. -/
theorem prizeFloor_of_subexp_moment_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℕ → ℝ} {c C A : ℝ} {r : ℕ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrA : (r : ℝ) ≤ A * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * (1 / c) * A ≤ C ^ 2)
    (henv : MomentEnvelope M 1 c)
    (henergyRep : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ r * M r) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_forall_rEnergy_le_mul_wick_depth_factor hψ G (by positivity) hC hGpos hq hr
    hrq hrA hconst
    (forall_rEnergy_le_mul_wick_of_subexp_moment G hc hc1 henv henergyRep)

end ProximityGap.Frontier.SubexpMomentToConvergenceHub

/-! ## Axiom audit -/
namespace ProximityGap.Frontier.SubexpMomentToConvergenceHub

#print axioms forall_rEnergy_le_mul_wick_of_subexp_moment_general
#print axioms nearRamanujan_of_subexp_moment_general_depth_factor
#print axioms prizeFloor_of_subexp_moment_general_depth_factor
#print axioms forall_rEnergy_le_mul_wick_of_subexp_moment
#print axioms nearRamanujan_of_subexp_moment_depth_factor
#print axioms prizeFloor_of_subexp_moment_depth_factor

end ProximityGap.Frontier.SubexpMomentToConvergenceHub
