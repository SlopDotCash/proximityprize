/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R160PuncturedUniqueBudgetConsumer

/-!
# LANE HLOW (#466 round 163): consumer-level contrapositive for the unique slice

R160 gives a full z-stratified weld consumer from the uniform punctured unique-decoding band,
leaving only far, fit, unsafe, and budget hypotheses explicit.  This file records the direct
contrapositive: once those explicit side hypotheses are fixed, any failure of the MCA-threshold
conclusion must refute the uniform punctured unique-decoding band.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LargeZeroWitnessSplit.Frontier.R163PuncturedUniqueConsumerContrapositive

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.FarCosetExplosion
open ProximityGap.LineListMCAWeld
open ProximityGap.LineListMCAWeld.SupportAware
open ProximityGap.LargeZeroWitnessSplit.Frontier.R160PuncturedUniqueBudgetConsumer

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- With the far, fit, unsafe, cap, and final-budget hypotheses fixed, failure of the target
MCA-threshold conclusion forces failure of the uniform punctured unique-decoding band. -/
theorem not_uniform_punctured_unique_of_not_mcaDeltaStar
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar Bunsafe Bcap : ℕ} (L : ℕ → ℕ)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : ∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁ (L ((directionZeroSet u₁).card)))
    (hfit : ∀ z : ℕ, z < a → L z * ((n - z) / (a - z)) ≤ Bfar)
    (hunsafe : ∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ Bunsafe)
    (hcap : max Bfar (max n Bunsafe) ≤ Bcap)
    (hBudget : (Bcap : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1)
    (hfail : ¬ δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar) :
    ¬ ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      (directionZeroSet u₁).card + k ≤ 2 * (a - (directionSupportSet u₁).card) := by
  intro hunique
  exact hfail
    (mcaDeltaStar_ge_of_zeroStratified_puncturedUnique_cap dom hk a δ εstar L
      haC haF hfarL hfit hunique hunsafe hcap hBudget hδ1)

end ProximityGap.LargeZeroWitnessSplit.Frontier.R163PuncturedUniqueConsumerContrapositive

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R163PuncturedUniqueConsumerContrapositive.not_uniform_punctured_unique_of_not_mcaDeltaStar
