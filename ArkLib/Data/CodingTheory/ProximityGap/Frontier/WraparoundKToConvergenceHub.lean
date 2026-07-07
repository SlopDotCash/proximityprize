/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.WraparoundKToTransferSlack
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConvergenceHub

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# From the explicit wraparound `K^r` envelope to the convergence hub

`WraparoundKToTransferSlack` proves that an all-depth explicit wraparound `K^r` envelope gives the
S1 per-frequency estimate

`‖η_b‖ ≤ sqrt (2 e K |G| r)`.

This file repackages that estimate at the canonical spectral/prize interface.  The only extra input
is the transparent scale comparison that the chosen order `r`, slack `K`, and prize constant `C`
indeed place `sqrt (2 e K |G| r)` below `C * sqrt (|G| log (q/|G|))`.
-/

open AddChar
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ProximityGap.Frontier.ConvergenceHub
open ProximityGap.Frontier.DCWickWraparoundTransfer
open ProximityGap.Frontier.WraparoundKToTransferSlack

namespace ProximityGap.Frontier.WraparoundKToConvergenceHub

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Square-root monotonicity in the exact form used by the hub bridge: if the squared S1 scale is
below `C^2` times the target variance scale, then the norm scale is below `C` times the target
standard-deviation scale. -/
theorem sqrt_le_const_sqrt_of_le_sq_mul {A B C : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hAB : A ≤ C ^ 2 * B) :
    Real.sqrt A ≤ C * Real.sqrt B := by
  calc
    Real.sqrt A ≤ Real.sqrt (C ^ 2 * B) := Real.sqrt_le_sqrt hAB
    _ = C * Real.sqrt B := by
      rw [show C ^ 2 * B = (C * Real.sqrt B) ^ 2 by
        rw [mul_pow, Real.sq_sqrt hB]]
      exact Real.sqrt_sq (mul_nonneg hC (Real.sqrt_nonneg B))

/-- A squared constant comparison discharges the explicit `hscale` needed by the convergence-hub
wrapper.  This is the bookkeeping step from
`2eK r ≤ C^2 log(q/|G|)` to
`sqrt(2eK |G| r) ≤ C sqrt(|G| log(q/|G|))`. -/
theorem s1Scale_le_prizeScale_of_core
    (G : Finset F) {K C : ℝ} {r : ℕ} (hC : 0 ≤ C)
    (hL :
      0 ≤ (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hcore :
      2 * Real.exp 1 * K * (r : ℝ)
        ≤ C ^ 2 * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))) :
    Real.sqrt (2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ))
      ≤ C * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))) := by
  have hn : 0 ≤ (G.card : ℝ) := by positivity
  apply sqrt_le_const_sqrt_of_le_sq_mul hC hL
  nlinarith [mul_le_mul_of_nonneg_left hcore hn]

/-- The target prize variance scale is nonnegative in the ordinary regime `0 < |G| ≤ q`. -/
theorem prizeVariance_nonneg_of_card_le (G : Finset F)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) :
    0 ≤ (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)) := by
  have hGposR : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast hGpos
  have hratio : (1 : ℝ) ≤ (Fintype.card F : ℝ) / (G.card : ℝ) :=
    (le_div_iff₀ hGposR).mpr (by simpa using hq)
  exact mul_nonneg hGposR.le (Real.log_nonneg hratio)

/-- An all-depth explicit wraparound `K^r` envelope reaches the spectral prize interface once its
S1 scale is no larger than the target near-Ramanujan-up-to-`sqrt log` scale. -/
theorem nearRamanujan_of_forall_q_wickExcess_le_mul_slack
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {K C : ℝ} {r : ℕ} (hK : 0 < K) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hscale :
      Real.sqrt (2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ))
        ≤ C * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))))
    (hgate : ∀ r : ℕ, 1 ≤ r →
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))) :
    NearRamanujanSqrtLog ψ G C := by
  intro b hb
  exact (eta_le_of_forall_q_wickExcess_le_mul_slack hψ G hK hr hrq hgate hb).trans hscale

/-- The same explicit wraparound `K^r` envelope lands in the convergence hub `PrizeFloor`, with the
scale comparison kept as a named hypothesis. -/
theorem prizeFloor_of_forall_q_wickExcess_le_mul_slack
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {K C : ℝ} {r : ℕ} (hK : 0 < K) (hC : 0 ≤ C)
    (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hscale :
      Real.sqrt (2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ))
        ≤ C * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))))
    (hgate : ∀ r : ℕ, 1 ≤ r →
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))) :
    PrizeFloor ψ G C :=
  prizeFloor_of_nearRamanujan hq hC
    (nearRamanujan_of_forall_q_wickExcess_le_mul_slack hψ G hK hr hrq hscale hgate)

/-- Hub-facing form with the scale comparison stated before taking square roots. -/
theorem nearRamanujan_of_forall_q_wickExcess_le_mul_slack_core
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {K C : ℝ} {r : ℕ} (hK : 0 < K) (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hL :
      0 ≤ (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hcore :
      2 * Real.exp 1 * K * (r : ℝ)
        ≤ C ^ 2 * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hgate : ∀ r : ℕ, 1 ≤ r →
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))) :
    NearRamanujanSqrtLog ψ G C :=
  nearRamanujan_of_forall_q_wickExcess_le_mul_slack hψ G hK hr hrq
    (s1Scale_le_prizeScale_of_core G hC hL hcore) hgate

/-- Prize-floor form with the scale comparison stated before taking square roots. -/
theorem prizeFloor_of_forall_q_wickExcess_le_mul_slack_core
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {K C : ℝ} {r : ℕ} (hK : 0 < K) (hC : 0 ≤ C)
    (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hL :
      0 ≤ (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hcore :
      2 * Real.exp 1 * K * (r : ℝ)
        ≤ C ^ 2 * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hgate : ∀ r : ℕ, 1 ≤ r →
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))) :
    PrizeFloor ψ G C :=
  prizeFloor_of_forall_q_wickExcess_le_mul_slack hψ G hK hC hq hr hrq
    (s1Scale_le_prizeScale_of_core G hC hL hcore) hgate

/-- Prize-floor form in the standard nonempty-subgroup regime, deriving nonnegativity of
`|G| log(q/|G|)` from `0 < |G| ≤ q`. -/
theorem prizeFloor_of_forall_q_wickExcess_le_mul_slack_core_card
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {K C : ℝ} {r : ℕ} (hK : 0 < K) (hC : 0 ≤ C)
    (hGpos : 0 < G.card) (hq : (G.card : ℝ) ≤ Fintype.card F) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hcore :
      2 * Real.exp 1 * K * (r : ℝ)
        ≤ C ^ 2 * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
    (hgate : ∀ r : ℕ, 1 ≤ r →
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))) :
    PrizeFloor ψ G C :=
  prizeFloor_of_forall_q_wickExcess_le_mul_slack_core hψ G hK hC hq hr hrq
    (prizeVariance_nonneg_of_card_le G hGpos hq) hcore hgate

end ProximityGap.Frontier.WraparoundKToConvergenceHub

/-! ## Axiom audit -/
namespace ProximityGap.Frontier.WraparoundKToConvergenceHub

#print axioms sqrt_le_const_sqrt_of_le_sq_mul
#print axioms s1Scale_le_prizeScale_of_core
#print axioms prizeVariance_nonneg_of_card_le
#print axioms nearRamanujan_of_forall_q_wickExcess_le_mul_slack
#print axioms prizeFloor_of_forall_q_wickExcess_le_mul_slack
#print axioms nearRamanujan_of_forall_q_wickExcess_le_mul_slack_core
#print axioms prizeFloor_of_forall_q_wickExcess_le_mul_slack_core
#print axioms prizeFloor_of_forall_q_wickExcess_le_mul_slack_core_card

end ProximityGap.Frontier.WraparoundKToConvergenceHub
