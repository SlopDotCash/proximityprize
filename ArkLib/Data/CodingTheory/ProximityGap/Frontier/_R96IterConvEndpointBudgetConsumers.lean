/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R95IterConvMultiStepPublicConstantConsumers
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R35FullConvLagEnergy

/-!
# LANE B2 (#466 round 96): endpoint budgets for multi-step Wick propagation

R95 exposes the exact budget needed at each intermediate depth:

`∀ t ∈ [r, r+k), (m : ℝ) ≤ C * (t+1)`.

Since the right-hand side is monotone in `t` when `C ≥ 0`, one endpoint budget at the starting
rung pays the entire interval.  In particular, every r = 3 propagation only needs the scalar
condition `(m : ℝ) ≤ 4 * C` (spelled as `C * 4` below to match the tower constants).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R31LagSpectrumWeilBound
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy
open ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter
open ArkLib.ProximityGap.Frontier.R91PointwiseTripleToIterWickBridge
open ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers

variable {m : ℕ} [NeZero m]

/-- A starting-depth budget pays every later R95 head-rung budget in the propagation interval. -/
theorem iterConvEnergyWick_add_of_prev_of_endpoint_budget_le_const
    (J : ZMod m → ℂ) (q r k : ℕ) {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hprev : IterConvEnergyWick J q r C)
    (hbudget₀ : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ)) :
    IterConvEnergyWick J q (r + k) C' :=
  iterConvEnergyWick_add_of_prev_of_budget_le_const J q r k hJ hC0 hCC hprev
    (fun t hrt _htk =>
      hbudget₀.trans
        (mul_le_mul_of_nonneg_left
          (Nat.cast_le.mpr (Nat.succ_le_succ hrt) : ((r + 1 : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ))
          hC0))

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Endpoint-budget multi-step propagation, immediately consumed by the pointwise face bound. -/
theorem sup_pureFace_add_of_iterConvEnergyWick_prev_of_endpoint_budget_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {r k : ℕ} {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hprev : IterConvEnergyWick J (Fintype.card F) r C)
    (hbudget₀ : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ))
    {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (r + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (r + k) * ((r + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (r + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const hfam hgrp J
    hJ hC0 hCC hprev
    (fun t hrt _htk =>
      hbudget₀.trans
        (mul_le_mul_of_nonneg_left
          (Nat.cast_le.mpr (Nat.succ_le_succ hrt) : ((r + 1 : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ))
          hC0))
    hs

/-- Lag-correlation control with the R35 zero-boundary budget starts the tower at `r = 2` and
then pays the whole tail from the single endpoint budget `m ≤ C * 3`. -/
theorem iterConvEnergyWick_from_two_of_lagCorrelation_bound_endpoint_le_const
    (J : ZMod m → ℂ) (q k : ℕ) {L B C₂ C C' : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B)
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (henergyBudget : 2 * ((m : ℝ) * L ^ 2)
        + (8 * (m : ℝ)) * ‖J 0‖ ^ 2 * B ^ 2
      ≤ C₂ * (m : ℝ) * (q : ℝ) ^ 2)
    (hC₂ : C₂ ≤ 2 * C ^ 2)
    (hJsq : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hbudget₂ : (m : ℝ) ≤ C * 3) :
    IterConvEnergyWick J q (2 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_endpoint_budget_le_const J q 2 k
    hJsq hC0 hCC
    (iterConvEnergyWick_two_of_lagCorrelation_bound_and_zeroBoundary_budget
      J q hB0 hJ hlag henergyBudget hC₂)
    (by simpa using hbudget₂)

/-- Zero-mode-free lag-correlation control starts the tower at `r = 2` and propagates from the
single endpoint budget `m ≤ C * 3`. -/
theorem iterConvEnergyWick_from_two_of_lagCorrelation_bound_of_zero_endpoint_le_const
    (J : ZMod m → ℂ) (q k : ℕ) (hJ0 : J 0 = 0) {L C₂ C C' : ℝ}
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (henergyBudget : (m : ℝ) * L ^ 2 ≤ C₂ * (m : ℝ) * (q : ℝ) ^ 2)
    (hC₂ : C₂ ≤ 2 * C ^ 2)
    (hJsq : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hbudget₂ : (m : ℝ) ≤ C * 3) :
    IterConvEnergyWick J q (2 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_endpoint_budget_le_const J q 2 k
    hJsq hC0 hCC
    (iterConvEnergyWick_two_of_lagCorrelation_bound_of_zero_budget
      J q hJ0 hlag henergyBudget hC₂)
    (by simpa using hbudget₂)

/-- Lag-correlation control with the R35 zero-boundary budget starts the tower at `r = 3` and
then pays the whole tail from the single endpoint budget `m ≤ C * 4`. -/
theorem iterConvEnergyWick_from_three_of_lagCorrelation_bound_endpoint_le_const
    (J : ZMod m → ℂ) (q k : ℕ) {L B C₃ C C' : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B)
    (hJsq : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (henergyBudget : 2 * ((m : ℝ) * L ^ 2)
        + (8 * (m : ℝ)) * ‖J 0‖ ^ 2 * B ^ 2
      ≤ C₃ * (m : ℝ) * (q : ℝ) ^ 2)
    (hC₃ : C₃ ≤ 6 * C ^ 3)
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hbudget₃ : (m : ℝ) ≤ C * 4) :
    IterConvEnergyWick J q (3 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_endpoint_budget_le_const J q 3 k
    hJsq hC0 hCC
    (iterConvEnergyWick_three_of_lagCorrelation_bound_and_zeroBoundary_budget
      J q hB0 hJ hJsq hlag henergyBudget hC₃)
    (by simpa using hbudget₃)

/-- Zero-mode-free lag-correlation control starts the tower at `r = 3` and propagates from the
single endpoint budget `m ≤ C * 4`. -/
theorem iterConvEnergyWick_from_three_of_lagCorrelation_bound_of_zero_endpoint_le_const
    (J : ZMod m → ℂ) (q k : ℕ) (hJ0 : J 0 = 0)
    (hJsq : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ)) {L C₃ C C' : ℝ}
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (henergyBudget : (m : ℝ) * L ^ 2 ≤ C₃ * (m : ℝ) * (q : ℝ) ^ 2)
    (hC₃ : C₃ ≤ 6 * C ^ 3)
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hbudget₃ : (m : ℝ) ≤ C * 4) :
    IterConvEnergyWick J q (3 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_endpoint_budget_le_const J q 3 k
    hJsq hC0 hCC
    (iterConvEnergyWick_three_of_lagCorrelation_bound_of_zero_budget
      J q hJ0 hJsq hlag henergyBudget hC₃)
    (by simpa using hbudget₃)

/-- The hzero-free Jacobi/Weil R35 max-budget starts the tower at `r = 2`, then the R96 endpoint
budget propagates it to `2+k`. -/
theorem iterConvEnergyWick_from_two_of_twoCharacterWeilInput_maxBudget_endpoint_le_const
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (k : ℕ) {Cweil B Ctwo C C' : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hJsq : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hheadBudget : 2 * ((m : ℝ)
        * (max ((m : ℝ) * B ^ 2)
            ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctwo * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hCtwo : Ctwo ≤ 2 * C ^ 2)
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hbudget₂ : (m : ℝ) ≤ C * 3) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) (2 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_endpoint_budget_le_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 2 k
    hJsq hC0 hCC
    (iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
      hχ hχ1 hfam hgrp hB0 hJ hweil hheadBudget hCtwo)
    (by simpa using hbudget₂)

/-- The hzero-free Jacobi/Weil R35 max-budget starts the tower at `r = 2`, propagates it to
`2+k`, and is immediately consumed by the pointwise pure-face bound. -/
theorem sup_pureFace_from_two_of_twoCharacterWeilInput_maxBudget_endpoint_le_const
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (k : ℕ) {Cweil B Ctwo C C' : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hJsq : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hheadBudget : 2 * ((m : ℝ)
        * (max ((m : ℝ) * B ^ 2)
            ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctwo * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hCtwo : Ctwo ≤ 2 * C ^ 2)
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hbudget₂ : (m : ℝ) ≤ C * 3)
    {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ (2 * (2 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (2 + k) * ((2 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (2 + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_endpoint_budget_le_const
    hfam hgrp (fun i : ZMod m => jacobiCoeff χ lam i)
    hJsq hC0 hCC
    (iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
      hχ hχ1 hfam hgrp hB0 hJ hweil hheadBudget hCtwo)
    (by simpa using hbudget₂)
    hs

/-- The hzero-free Jacobi/Weil R35 max-budget starts the tower at `r = 3`, then the R96 endpoint
budget propagates it to `3+k`. -/
theorem iterConvEnergyWick_from_three_of_twoCharacterWeilInput_maxBudget_endpoint_le_const
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (k : ℕ) {Cweil B Ctriple C C' : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hheadBudget : 2 * ((m : ℝ)
        * (max ((m : ℝ) * B ^ 2)
            ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hCtriple : Ctriple ≤ 6 * C ^ 3)
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hbudget₃ : (m : ℝ) ≤ C * 4) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) (3 + k) C' := by
  have hJsq : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ^ 2 ≤ (Fintype.card F : ℝ) := by
    intro c
    exact (pow_le_pow_left₀ (norm_nonneg _) (hJ c) 2).trans hBsq
  exact iterConvEnergyWick_add_of_prev_of_endpoint_budget_le_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 3 k
    hJsq hC0 hCC
    (iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
      hχ hχ1 hfam hgrp hB0 hJ hBsq hweil hheadBudget hCtriple)
    (by simpa using hbudget₃)

/-- The hzero-free Jacobi/Weil R35 max-budget starts the tower at `r = 3`, propagates it to
`3+k`, and is immediately consumed by the pointwise pure-face bound. -/
theorem sup_pureFace_from_three_of_twoCharacterWeilInput_maxBudget_endpoint_le_const
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (k : ℕ) {Cweil B Ctriple C C' : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hheadBudget : 2 * ((m : ℝ)
        * (max ((m : ℝ) * B ^ 2)
            ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hCtriple : Ctriple ≤ 6 * C ^ 3)
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hbudget₃ : (m : ℝ) ≤ C * 4)
    {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) := by
  have hJsq : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ^ 2 ≤ (Fintype.card F : ℝ) := by
    intro c
    exact (pow_le_pow_left₀ (norm_nonneg _) (hJ c) 2).trans hBsq
  exact sup_pureFace_add_of_iterConvEnergyWick_prev_of_endpoint_budget_le_const
    hfam hgrp (fun i : ZMod m => jacobiCoeff χ lam i)
    hJsq hC0 hCC
    (iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
      hχ hχ1 hfam hgrp hB0 hJ hBsq hweil hheadBudget hCtriple)
    (by simpa using hbudget₃)
    hs

/-- A calibrated r = 3 energy certificate propagates to depth `3+k` from the single endpoint
budget `m ≤ C * 4`. -/
theorem iterConvEnergyWick_from_three_of_tripleConvEnergyBound_endpoint_le_const
    (J : ZMod m → ℂ) (q k : ℕ) {B C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget₃ : (m : ℝ) ≤ C * 4)
    (h : TripleConvEnergyBound J q B) :
    IterConvEnergyWick J q (3 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_endpoint_budget_le_const J q 3 k hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvEnergyBound J q hBC h)
    (by simpa using hbudget₃)

/-- A calibrated r = 3 energy certificate propagates to depth `3+k` and is immediately consumed
by the public face-moment bound, using only the endpoint budget `m ≤ C * 4`. -/
theorem sup_pureFace_from_three_of_tripleConvEnergyBound_endpoint_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {B C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget₃ : (m : ℝ) ≤ C * 4)
    (h : TripleConvEnergyBound J (Fintype.card F) B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_endpoint_budget_le_const hfam hgrp J
    hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvEnergyBound J (Fintype.card F) hBC h)
    (by simpa using hbudget₃)
    hs

/-- A pointwise r = 3 certificate propagates to depth `3+k` from the single endpoint budget
`m ≤ C * 4`. -/
theorem iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_endpoint_le_const
    (J : ZMod m → ℂ) (q k : ℕ) {B B' C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget₃ : (m : ℝ) ≤ C * 4)
    (hpt : TripleConvPointwiseBound J q B) :
    IterConvEnergyWick J q (3 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_endpoint_budget_le_const J q 3 k hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le J q hBB hBC hpt)
    (by simpa using hbudget₃)

/-- A pointwise r = 3 certificate propagates to depth `3+k` and is immediately consumed by the
public face-moment bound, using only the endpoint budget `m ≤ C * 4`. -/
theorem sup_pureFace_from_three_of_tripleConvPointwiseBound_endpoint_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {B B' C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget₃ : (m : ℝ) ≤ C * 4)
    (hpt : TripleConvPointwiseBound J (Fintype.card F) B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_endpoint_budget_le_const hfam hgrp J
    hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le
      J (Fintype.card F) hBB hBC hpt)
    (by simpa using hbudget₃)
    hs

/-- The r = 3 endpoint budget is equivalent to paying a linear-in-`m` Wick constant up to the
factor `4`; this records the arithmetic obstruction carried by the bare Cauchy recursion. -/
theorem le_const_of_three_endpoint_budget {C : ℝ}
    (hbudget₃ : (m : ℝ) ≤ C * 4) :
    (m : ℝ) / 4 ≤ C := by
  nlinarith

/-- A bounded public constant below `m/4` cannot satisfy the r = 3 endpoint budget. -/
theorem not_three_endpoint_budget_of_const_lt {C K : ℝ}
    (hCK : C ≤ K) (hK : K * 4 < (m : ℝ)) :
    ¬ (m : ℝ) ≤ C * 4 := by
  intro hbudget₃
  nlinarith

/-- Jacobi six-input propagation from the r = 3 head to depth `3+k`, with only the endpoint
budget `m ≤ C * 4`. -/
theorem iterConvEnergyWick_from_three_of_jacobiHermitianSixInput_endpoint_le_const
    {B B' C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget₃ : (m : ℝ) ≤ C * 4)
    (h : JacobiHermitianSixInput χ lam B) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) (3 + k) C' :=
  iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_endpoint_le_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) k
    hJ hC0 hCC hBB hBC hbudget₃
    ((jacobiHermitianSixInput_iff_tripleConvPointwiseBound
      (χ := χ) (lam := lam) (C := B)).mp h)

/-- Jacobi six-input propagation from the r = 3 head, consumed by the public face-moment bound,
with only the endpoint budget `m ≤ C * 4`. -/
theorem sup_pureFace_from_three_of_jacobiHermitianSixInput_endpoint_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B B' C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget₃ : (m : ℝ) ≤ C * 4)
    (h : JacobiHermitianSixInput χ lam B) {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_endpoint_budget_le_const hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i)
    hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F)
      hBB hBC
      ((jacobiHermitianSixInput_iff_tripleConvPointwiseBound
        (χ := χ) (lam := lam) (C := B)).mp h))
    (by simpa using hbudget₃)
    hs

end ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.iterConvEnergyWick_add_of_prev_of_endpoint_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.sup_pureFace_add_of_iterConvEnergyWick_prev_of_endpoint_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.iterConvEnergyWick_from_two_of_lagCorrelation_bound_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.iterConvEnergyWick_from_two_of_lagCorrelation_bound_of_zero_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.iterConvEnergyWick_from_three_of_lagCorrelation_bound_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.iterConvEnergyWick_from_three_of_lagCorrelation_bound_of_zero_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.iterConvEnergyWick_from_two_of_twoCharacterWeilInput_maxBudget_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.sup_pureFace_from_two_of_twoCharacterWeilInput_maxBudget_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.iterConvEnergyWick_from_three_of_twoCharacterWeilInput_maxBudget_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.sup_pureFace_from_three_of_twoCharacterWeilInput_maxBudget_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.iterConvEnergyWick_from_three_of_tripleConvEnergyBound_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.sup_pureFace_from_three_of_tripleConvEnergyBound_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.sup_pureFace_from_three_of_tripleConvPointwiseBound_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.le_const_of_three_endpoint_budget
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.not_three_endpoint_budget_of_const_lt
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.iterConvEnergyWick_from_three_of_jacobiHermitianSixInput_endpoint_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers.sup_pureFace_from_three_of_jacobiHermitianSixInput_endpoint_le_const
