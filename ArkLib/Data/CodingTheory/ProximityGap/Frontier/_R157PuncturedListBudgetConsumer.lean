/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._LowProfileFiberCoupled
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportAwareWeldConsumer

/-!
# LANE W6 (#466 round 157): direct punctured-list budgets feed the z-stratified weld

`_LowProfileFiberCoupled.lean` identifies the surviving large-zero-safe object:
`PuncturedListBudget`.  The old low-profile route bounded each coordinate fiber and then paid the
exploded `choose(z,t)` sum; the corrected route bounds the punctured appearing list directly and
pays only the support factor.

This file packages that positive consumer.  A direct punctured-list budget `Λ ≤ B` on
large-zero-safe directions gives a safe large-zero bad-scalar budget `≤ B*n`; composed with the
z-stratified far branch and unsafe branch of `_SupportAwareWeldConsumer.lean`, it yields the same
`δ ≤ mcaDeltaStar` conclusion.  The hard input remains exactly the direct punctured-list theorem,
not the refuted coupled-sum/fiber envelope.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LineListMCAWeld.SupportAware.Frontier.R157PuncturedListBudgetConsumer

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.FarCosetExplosion
open ProximityGap.LineListMCAWeld
open ProximityGap.LineListMCAWeld.SupportAware
open ProximityGap.LowProfileCoupled

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- A direct punctured-list budget supplies the large-zero residual hypothesis expected by the
z-stratified weld: safe large-zero lines are served by `PuncturedListBudget`, unsafe large-zero
lines remain in the explicit `hunsafe` branch. -/
theorem largeZeroResidualBudgeted_of_puncturedListBudget
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) {B Bunsafe : ℕ}
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hpunctured : PuncturedListBudget dom k a B)
    (hunsafe : ∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ Bunsafe) :
    ∀ u₀ e₁ : Fin n → F, a ≤ (directionZeroSet e₁).card →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ e₁ γ)).card
        ≤ max (B * n) Bunsafe :=
  lowWeight_badCount_le_of_largeZeroSafe_budget dom k a δ haF
    (largeZeroSafeLineBadScalarsBudgeted_of_puncturedListBudget dom k a B hpunctured)
    hunsafe

open Classical in
/-- **Punctured-list consumer for the z-stratified weld.**  Far directions are handled by the
zero-count-dependent list budget `L`; large-zero-safe directions are handled by the direct
`PuncturedListBudget`; unsafe large-zero directions stay as the explicit `hunsafe` budget. -/
theorem mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar Bpunctured Bunsafe : ℕ} (L : ℕ → ℕ)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : ∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁ (L ((directionZeroSet u₁).card)))
    (hfit : ∀ z : ℕ, z < a → L z * ((n - z) / (a - z)) ≤ Bfar)
    (hpunctured : PuncturedListBudget dom k a Bpunctured)
    (hunsafe : ∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ Bunsafe)
    (hBudget :
      ((max Bfar (max (Bpunctured * n) Bunsafe) : ℕ) : ℝ≥0∞) /
          (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  mcaDeltaStar_ge_of_farLineListBudgeted_zeroStratified dom k a δ εstar L haC haF
    hfarL hfit
    (largeZeroResidualBudgeted_of_puncturedListBudget dom k a δ haF hpunctured hunsafe)
    hBudget hδ1

end ProximityGap.LineListMCAWeld.SupportAware.Frontier.R157PuncturedListBudgetConsumer

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LineListMCAWeld.SupportAware.Frontier.R157PuncturedListBudgetConsumer.largeZeroResidualBudgeted_of_puncturedListBudget
#print axioms
  ProximityGap.LineListMCAWeld.SupportAware.Frontier.R157PuncturedListBudgetConsumer.mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget
