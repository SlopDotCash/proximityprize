/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R159PuncturedUniqueDecodingSlice
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R159PuncturedListBudgetCapConsumer

/-!
# LANE HLOW (#466 round 160): punctured unique decoding feeds the punctured-list socket

R159 proves the per-line unique-decoding slice:

`#Z + k ≤ 2 * (a - #support(u₁)) ⟹ #lineAppearingCodewords ≤ 1`.

This file packages the uniform version as an input to the R157/R159 punctured-list weld consumer.
It is intentionally conditional on a strong geometric band hypothesis, and therefore not
prize-closing; it cleanly records the exact region where the punctured-list residual becomes the
trivial budget `B = 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LargeZeroWitnessSplit.Frontier.R160PuncturedUniqueBudgetConsumer

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.FarCosetExplosion
open ProximityGap.LineListMCAWeld
open ProximityGap.LineListMCAWeld.SupportAware
open ProximityGap.LowProfileCoupled
open ProximityGap.LargeZeroWitnessSplit.Frontier.R159PuncturedUniqueDecodingSlice
open ProximityGap.LineListMCAWeld.SupportAware.Frontier.R159PuncturedListBudgetCapConsumer

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Uniform punctured unique-decoding hypotheses give the direct punctured-list budget with
budget `1`. -/
theorem puncturedListBudget_one_of_uniform_punctured_unique
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (hunique : ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      (directionZeroSet u₁).card + k ≤ 2 * (a - (directionSupportSet u₁).card)) :
    PuncturedListBudget dom k a 1 := by
  intro u₀ u₁ hne _hsafe
  exact lineAppearingCodewords_card_le_one_of_punctured_unique dom hk a u₀ u₁
    (hunique u₁ hne)

open Classical in
/-- The unique-decoding slice gives a large-zero-safe bad-scalar budget `≤ n`, via the direct
punctured-list route. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_uniform_punctured_unique
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (hunique : ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      (directionZeroSet u₁).card + k ≤ 2 * (a - (directionSupportSet u₁).card)) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a n := by
  simpa using
    (largeZeroSafeLineBadScalarsBudgeted_of_puncturedListBudget dom k a 1
      (puncturedListBudget_one_of_uniform_punctured_unique dom hk a hunique))

open Classical in
/-- Single-cap MCA-threshold consumer for the punctured unique-decoding band.  The large-zero-safe
branch spends only `n`; far and unsafe branches remain explicit. -/
theorem mcaDeltaStar_ge_of_zeroStratified_puncturedUnique_cap
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar Bunsafe Bcap : ℕ} (L : ℕ → ℕ)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : ∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁ (L ((directionZeroSet u₁).card)))
    (hfit : ∀ z : ℕ, z < a → L z * ((n - z) / (a - z)) ≤ Bfar)
    (hunique : ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      (directionZeroSet u₁).card + k ≤ 2 * (a - (directionSupportSet u₁).card))
    (hunsafe : ∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ Bunsafe)
    (hcap : max Bfar (max n Bunsafe) ≤ Bcap)
    (hBudget : (Bcap : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget_cap dom k a δ εstar L
    haC haF hfarL hfit
    (puncturedListBudget_one_of_uniform_punctured_unique dom hk a hunique)
    hunsafe
    (by simpa using hcap)
    hBudget hδ1

end ProximityGap.LargeZeroWitnessSplit.Frontier.R160PuncturedUniqueBudgetConsumer

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R160PuncturedUniqueBudgetConsumer.puncturedListBudget_one_of_uniform_punctured_unique
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R160PuncturedUniqueBudgetConsumer.largeZeroSafeLineBadScalarsBudgeted_of_uniform_punctured_unique
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R160PuncturedUniqueBudgetConsumer.mcaDeltaStar_ge_of_zeroStratified_puncturedUnique_cap
