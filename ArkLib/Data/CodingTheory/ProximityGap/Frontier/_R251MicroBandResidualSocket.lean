/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R251 micro-band residual socket)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# R251 (#466): micro-band residual CDF socket

R249/R251 split the trim-five residual tail into:

* a micro-band count cap at `τ`, used only up to `κ`;
* a half-rate tail cap from `κ` onward.

This file packages the finite-carrier accounting.  It proves no arithmetic
distribution theorem; the two hypotheses below are the narrowed analytic
obligations for the quotient Gauss-period residual carrier.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R251MicroBandResidualSocket

variable {ι : Type*} [DecidableEq ι]

noncomputable section

/-- Residual survivor count at threshold `θ`. -/
def SurvivorCount (s : Finset ι) (t : ι → ℝ) (θ : ℝ) : ℝ :=
  ((s.filter (fun i => θ ≤ t i)).card : ℝ)

/-- A micro-band cap at `τ`, valid on `[τ, κ)`, plus a half-rate tail from `κ`. -/
def MicroBandHalfRateSplit (s : Finset ι) (t : ι → ℝ)
    (τ κ Cmicro Ctail : ℝ) : Prop :=
  SurvivorCount s t τ ≤ Cmicro * (s.card : ℝ) ∧
    ∀ θ, κ ≤ θ → SurvivorCount s t θ ≤
      Ctail * (s.card : ℝ) * Real.exp (-(θ / 2))

/-- The micro-band split implies the target half-rate envelope at every
threshold above `τ`, provided the micro-band endpoint fits the same constant. -/
theorem residual_tail_of_microBandHalfRateSplit
    (s : Finset ι) (t : ι → ℝ) {τ κ Cmicro Ctail C : ℝ}
    (hτκ : τ ≤ κ)
    (hCmicro : Cmicro * Real.exp (κ / 2) ≤ C)
    (hCtail : Ctail ≤ C)
    (hSplit : MicroBandHalfRateSplit s t τ κ Cmicro Ctail)
    (θ : ℝ) (hτθ : τ ≤ θ) :
    SurvivorCount s t θ ≤ C * (s.card : ℝ) * Real.exp (-(θ / 2)) := by
  by_cases hκθ : κ ≤ θ
  · have htail := hSplit.2 θ hκθ
    have hcard_nonneg : 0 ≤ (s.card : ℝ) := by exact_mod_cast Nat.zero_le s.card
    have hexp_nonneg : 0 ≤ Real.exp (-(θ / 2)) := le_of_lt (Real.exp_pos _)
    calc
      SurvivorCount s t θ ≤ Ctail * (s.card : ℝ) * Real.exp (-(θ / 2)) := htail
      _ ≤ C * (s.card : ℝ) * Real.exp (-(θ / 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCtail hcard_nonneg) hexp_nonneg
  · have hθκ : θ ≤ κ := le_of_not_ge hκθ
    have hsubset :
        s.filter (fun i => θ ≤ t i) ⊆ s.filter (fun i => τ ≤ t i) := by
      intro i hi
      have his : i ∈ s := (Finset.mem_filter.mp hi).1
      have hθt : θ ≤ t i := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨his, le_trans hτθ hθt⟩
    have hcount :
        SurvivorCount s t θ ≤ SurvivorCount s t τ := by
      unfold SurvivorCount
      exact_mod_cast Finset.card_le_card hsubset
    have hmicro : SurvivorCount s t τ ≤ Cmicro * (s.card : ℝ) := hSplit.1
    have hmicro_rhs_nonneg : 0 ≤ Cmicro * (s.card : ℝ) := by
      have hsurv_nonneg : 0 ≤ SurvivorCount s t τ := by
        unfold SurvivorCount
        exact_mod_cast Nat.zero_le (s.filter (fun i => τ ≤ t i)).card
      exact le_trans hsurv_nonneg hmicro
    have htheta_nonneg : 0 ≤ Real.exp (θ / 2) := le_of_lt (Real.exp_pos _)
    have hmul :
        SurvivorCount s t θ * Real.exp (θ / 2) ≤ C * (s.card : ℝ) := by
      calc
        SurvivorCount s t θ * Real.exp (θ / 2)
            ≤ (Cmicro * (s.card : ℝ)) * Real.exp (θ / 2) := by
          exact mul_le_mul_of_nonneg_right (le_trans hcount hmicro) htheta_nonneg
        _ ≤ (Cmicro * (s.card : ℝ)) * Real.exp (κ / 2) := by
          have hExp : Real.exp (θ / 2) ≤ Real.exp (κ / 2) :=
            Real.exp_le_exp.mpr (by linarith)
          exact mul_le_mul_of_nonneg_left hExp hmicro_rhs_nonneg
        _ = (Cmicro * Real.exp (κ / 2)) * (s.card : ℝ) := by ring
        _ ≤ C * (s.card : ℝ) := by
          exact mul_le_mul_of_nonneg_right hCmicro (by exact_mod_cast Nat.zero_le s.card)
    have hexp_pos : 0 < Real.exp (θ / 2) := Real.exp_pos _
    have hrewrite :
        C * (s.card : ℝ) =
          (C * (s.card : ℝ) * Real.exp (-(θ / 2))) * Real.exp (θ / 2) := by
      have hExpCancel : Real.exp (-(θ / 2)) * Real.exp (θ / 2) = 1 := by
        rw [← Real.exp_add]
        have hsum : -(θ / 2) + θ / 2 = 0 := by ring
        rw [hsum, Real.exp_zero]
      rw [mul_assoc, hExpCancel, mul_one]
    have htarget_mul :
        SurvivorCount s t θ * Real.exp (θ / 2) ≤
          (C * (s.card : ℝ) * Real.exp (-(θ / 2))) * Real.exp (θ / 2) := by
      simpa [← hrewrite] using hmul
    exact le_of_mul_le_mul_right htarget_mul hexp_pos

end

end ArkLib.ProximityGap.Frontier.R251MicroBandResidualSocket

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R251MicroBandResidualSocket.residual_tail_of_microBandHalfRateSplit
