/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.OptimizedSupFromWraparoundK
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS1_transfer_slack_prize

/-!
# From the explicit wraparound `K^r` envelope to the S1 transfer-slack residual

`_wfS1_transfer_slack_prize` records the abstract residual
`CharPEnergyTransferWithSlack Er n K`.  The newer wraparound files express the same target in the
more concrete `wickExcess` language.

This file welds the two: an all-depth explicit wraparound `K^r` envelope gives the S1 transfer
hypothesis for the actual nonprincipal averaged energy.
-/

open scoped BigOperators
open Finset AddChar
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.WFS1
open ProximityGap.Frontier.DCWickWraparoundTransfer
open ProximityGap.Frontier.OptimizedSupFromWraparoundK

namespace ProximityGap.Frontier.WraparoundKToTransferSlack

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The nonprincipal averaged `2r`-moment used by the S1 transfer-slack residual. -/
noncomputable def nonprincipalAvgEnergy (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) : ℝ :=
  ((∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) : ℝ) / (Fintype.card F : ℝ)

/-- The concrete nonprincipal average is `(q*E_r - |G|^(2r))/q`. -/
theorem nonprincipalAvgEnergy_eq_dc_quotient {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) :
    nonprincipalAvgEnergy ψ G r
      = ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r))
          / (Fintype.card F : ℝ) := by
  unfold nonprincipalAvgEnergy
  rw [sum_nonzero_moment hψ G r]

/-- A single-depth `K^r` wraparound envelope gives the S1 averaged-energy inequality. -/
theorem nonprincipalAvgEnergy_le_of_q_wickExcess_le_mul_slack {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ} {K : ℝ}
    (hgate :
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))) :
    nonprincipalAvgEnergy ψ G r
      ≤ K ^ r * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  have hK :=
    nonprincipalWickBoundK_of_q_wickExcess_le_mul_slack
      (F := F) hψ (G := G) (r := r) (K := K) hgate
  unfold nonprincipalAvgEnergy
  unfold OptimizedSupFromNonprincipalWick.NonprincipalWickBoundK at hK
  have hqpos : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hdiv := div_le_div_of_nonneg_right hK (le_of_lt hqpos)
  calc
    (∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) / (Fintype.card F : ℝ)
        ≤ ((Fintype.card F : ℝ)
            * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)))
            / (Fintype.card F : ℝ) := hdiv
    _ = K ^ r * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
        field_simp [ne_of_gt hqpos]

/-- An all-depth explicit wraparound `K^r` envelope is exactly an S1 transfer-slack input for the
actual nonprincipal averaged energy. -/
theorem transferSlack_of_forall_q_wickExcess_le_mul_slack {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) (K : ℝ)
    (hgate : ∀ r : ℕ, 1 ≤ r →
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))) :
    CharPEnergyTransferWithSlack (nonprincipalAvgEnergy ψ G) (G.card : ℝ) K := by
  intro r hr
  exact nonprincipalAvgEnergy_le_of_q_wickExcess_le_mul_slack hψ (hgate r hr)

/-- A single nonzero frequency is bounded by the nonprincipal averaged moment after multiplying
back by `q = |F|`. -/
theorem eta_pow_le_card_mul_nonprincipalAvgEnergy {ψ : AddChar F ℂ}
    (G : Finset F) (r : ℕ) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * nonprincipalAvgEnergy ψ G r := by
  have hterm :
      ‖eta ψ G b‖ ^ (2 * r)
        ≤ ∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) := by
    apply Finset.single_le_sum (f := fun b' => ‖eta ψ G b'‖ ^ (2 * r))
    · intro b' _
      positivity
    · exact Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  unfold nonprincipalAvgEnergy
  have hqpos : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  calc
    ‖eta ψ G b‖ ^ (2 * r)
        ≤ ∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) := hterm
    _ = (Fintype.card F : ℝ)
          * ((∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r))
              / (Fintype.card F : ℝ)) := by
        field_simp [ne_of_gt hqpos]

/-- S1 prize-square consumer with the residual stated as the explicit all-depth wraparound
`K^r` envelope. -/
theorem prize_sq_of_forall_q_wickExcess_le_mul_slack
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M K : ℝ} {r : ℕ}
    (hM : 0 ≤ M) (hK : 0 < K) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hgate : ∀ r : ℕ, 1 ≤ r →
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)))
    (hmoment :
      M ^ (2 * r) ≤ (Fintype.card F : ℝ) * nonprincipalAvgEnergy ψ G r) :
    M ^ 2 ≤ 2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ) := by
  have hn : 0 ≤ (G.card : ℝ) := by positivity
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  exact prize_sq_of_transfer_slack hM hn hq hK hr hrq
    (transferSlack_of_forall_q_wickExcess_le_mul_slack hψ G K hgate) hmoment

/-- S1 norm-form prize consumer with the residual stated as the explicit all-depth wraparound
`K^r` envelope. -/
theorem prize_of_forall_q_wickExcess_le_mul_slack
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M K : ℝ} {r : ℕ}
    (hM : 0 ≤ M) (hK : 0 < K) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hgate : ∀ r : ℕ, 1 ≤ r →
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)))
    (hmoment :
      M ^ (2 * r) ≤ (Fintype.card F : ℝ) * nonprincipalAvgEnergy ψ G r) :
    M ≤ Real.sqrt (2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ)) := by
  have hn : 0 ≤ (G.card : ℝ) := by positivity
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  exact prize_of_transfer_slack hM hn hq hK hr hrq
    (transferSlack_of_forall_q_wickExcess_le_mul_slack hψ G K hgate) hmoment

/-- Per-frequency S1 square bound from the explicit all-depth wraparound `K^r` envelope. -/
theorem eta_sq_le_of_forall_q_wickExcess_le_mul_slack
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {K : ℝ} {r : ℕ} (hK : 0 < K) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hgate : ∀ r : ℕ, 1 ≤ r →
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)))
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ) := by
  exact prize_sq_of_forall_q_wickExcess_le_mul_slack hψ G (norm_nonneg _) hK hr hrq hgate
    (eta_pow_le_card_mul_nonprincipalAvgEnergy G r hb)

/-- Per-frequency S1 norm bound from the explicit all-depth wraparound `K^r` envelope. -/
theorem eta_le_of_forall_q_wickExcess_le_mul_slack
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {K : ℝ} {r : ℕ} (hK : 0 < K) (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F : ℝ) ≤ r)
    (hgate : ∀ r : ℕ, 1 ≤ r →
      (Fintype.card F : ℝ) * wickExcess G r
        ≤ (Fintype.card F : ℝ)
            * ((K ^ r - 1)
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)))
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ≤ Real.sqrt (2 * Real.exp 1 * K * (G.card : ℝ) * (r : ℝ)) := by
  exact prize_of_forall_q_wickExcess_le_mul_slack hψ G (norm_nonneg _) hK hr hrq hgate
    (eta_pow_le_card_mul_nonprincipalAvgEnergy G r hb)

end ProximityGap.Frontier.WraparoundKToTransferSlack

/-! ## Axiom audit -/
namespace ProximityGap.Frontier.WraparoundKToTransferSlack

#print axioms nonprincipalAvgEnergy_eq_dc_quotient
#print axioms nonprincipalAvgEnergy_le_of_q_wickExcess_le_mul_slack
#print axioms transferSlack_of_forall_q_wickExcess_le_mul_slack
#print axioms eta_pow_le_card_mul_nonprincipalAvgEnergy
#print axioms prize_sq_of_forall_q_wickExcess_le_mul_slack
#print axioms prize_of_forall_q_wickExcess_le_mul_slack
#print axioms eta_sq_le_of_forall_q_wickExcess_le_mul_slack
#print axioms eta_le_of_forall_q_wickExcess_le_mul_slack

end ProximityGap.Frontier.WraparoundKToTransferSlack
