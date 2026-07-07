/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.WraparoundKToConvergenceHub

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# From ordinary energy slack to the explicit wraparound `K^r` gate

Several frontier lanes naturally produce the multiplicative energy envelope

`rEnergy G r ≤ K^r * (2r-1)!! * |G|^r`.

The newer wraparound route consumes the same information in excess form:

`q * wickExcess G r ≤ q * ((K^r - 1) * (2r-1)!! * |G|^r)`.

This file is the adapter between those two equivalent normalizations, and then composes it with the
hub-facing wraparound bridge.
-/

open AddChar
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ProximityGap.Frontier.DCWickWraparoundTransfer
open ProximityGap.Frontier.WraparoundKToConvergenceHub

namespace ProximityGap.Frontier.EnergySlackToWraparoundK

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A single-depth multiplicative energy slack bound implies the explicit wraparound-excess gate
used by the `K^r` route. -/
theorem q_wickExcess_le_mul_slack_of_rEnergy_le_mul_wick
    (G : Finset F) {K : ℝ} {r : ℕ}
    (henergy :
      (rEnergy G r : ℝ)
        ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :
    (Fintype.card F : ℝ) * wickExcess G r
      ≤ (Fintype.card F : ℝ)
          * ((K ^ r - 1)
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
  unfold wickExcess
  have hqnn : 0 ≤ (Fintype.card F : ℝ) := by positivity
  have hsub :
      (rEnergy G r : ℝ)
          - (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ (K ^ r - 1)
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
    nlinarith
  exact mul_le_mul_of_nonneg_left hsub hqnn

/-- All-depth multiplicative energy slack gives the all-depth explicit wraparound `K^r` gate. -/
theorem forall_q_wickExcess_le_mul_slack_of_forall_rEnergy_le_mul_wick
    (G : Finset F) {K : ℝ}
    (henergy : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ)
        ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :
    ∀ r : ℕ, 1 ≤ r →
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
  intro r hr
  exact q_wickExcess_le_mul_slack_of_rEnergy_le_mul_wick G (henergy r hr)

/-- Hub-facing prize-floor consumer stated in the ordinary multiplicative-energy language. -/
theorem prizeFloor_of_forall_rEnergy_le_mul_wick_core_card
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {K C : ℝ} {r : ℕ} (hK : 0 < K) (hC : 0 ≤ C)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hcore :
      2 * Real.exp 1 * K * (r : ℝ)
        ≤ C ^ 2 * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (henergy : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ)
        ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_forall_q_wickExcess_le_mul_slack_core_card hψ G hK hC hGpos hq hr hrq
    hcore (forall_q_wickExcess_le_mul_slack_of_forall_rEnergy_le_mul_wick G henergy)

/-- Constant bookkeeping for the prize scale.  If the chosen depth satisfies
`r ≤ A * log(q/|G|)` and the final constant budget satisfies `2eKA ≤ C²`, then the squared core
scale condition required by the hub bridge follows. -/
theorem core_scale_of_depth_le_log_mul
    (G : Finset F) {K C A : ℝ} {r : ℕ}
    (hK : 0 ≤ K)
    (hlog : 0 ≤ Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hrA : (r : ℝ) ≤ A * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * K * A ≤ C ^ 2) :
    2 * Real.exp 1 * K * (r : ℝ)
      ≤ C ^ 2 * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) := by
  have hcoef : 0 ≤ 2 * Real.exp 1 * K := by positivity
  have hmul := mul_le_mul_of_nonneg_left hrA hcoef
  calc
    2 * Real.exp 1 * K * (r : ℝ)
        ≤ 2 * Real.exp 1 * K *
            (A * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))) := hmul
    _ = (2 * Real.exp 1 * K * A)
          * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) := by ring
    _ ≤ C ^ 2 * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hconst hlog

/-- Hub-facing prize-floor consumer stated with a depth-factor hypothesis rather than the raw
squared scale inequality. -/
theorem prizeFloor_of_forall_rEnergy_le_mul_wick_depth_factor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {K C A : ℝ} {r : ℕ} (hKpos : 0 < K) (hC : 0 ≤ C)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hrA : (r : ℝ) ≤ A * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hconst : 2 * Real.exp 1 * K * A ≤ C ^ 2)
    (henergy : ∀ r : ℕ, 1 ≤ r →
      (rEnergy G r : ℝ)
        ≤ K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) :
    ConvergenceHub.PrizeFloor ψ G C :=
  prizeFloor_of_forall_rEnergy_le_mul_wick_core_card hψ G hKpos hC hGpos hq hr hrq
    (core_scale_of_depth_le_log_mul G hKpos.le
      (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hGpos : (0 : ℝ) < (G.card : ℝ))).mpr
        (by simpa using hq)))
      hrA hconst) henergy

end ProximityGap.Frontier.EnergySlackToWraparoundK

/-! ## Axiom audit -/
namespace ProximityGap.Frontier.EnergySlackToWraparoundK

#print axioms q_wickExcess_le_mul_slack_of_rEnergy_le_mul_wick
#print axioms forall_q_wickExcess_le_mul_slack_of_forall_rEnergy_le_mul_wick
#print axioms prizeFloor_of_forall_rEnergy_le_mul_wick_core_card
#print axioms core_scale_of_depth_le_log_mul
#print axioms prizeFloor_of_forall_rEnergy_le_mul_wick_depth_factor

end ProximityGap.Frontier.EnergySlackToWraparoundK
