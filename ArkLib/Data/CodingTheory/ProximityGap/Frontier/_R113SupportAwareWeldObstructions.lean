/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportAwareWeldConsumer

/-!
# Obstructions for the support-aware line-list weld

`_SupportAwareWeldConsumer.lean` strengthens the prize-facing line-list weld by allowing the
far-line budget to depend on the direction zero count.  This file records the corresponding
contrapositives: a failed `mcaDeltaStar` floor rules out the whole z-stratified production package.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LineListMCAWeld.SupportAware.Frontier.R113SupportAwareWeldObstructions

open ProximityGap.LineListMCAWeld.SupportAware
open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.FarCosetExplosion

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Z-stratified weld obstruction: if the `δ*` floor fails, then the zero-count-stratified
far-line list budget, its arithmetic fit, the large-zero budget, and the normalized budget
cannot all hold. -/
theorem not_zeroStratified_weld_package_of_mcaDeltaStar_floor_failure
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar Bnear : ℕ} (L : ℕ → ℕ)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfail :
      ¬ δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar) :
    ¬ ((∀ u₀ u₁ : Fin n → F,
          FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
            LineListBudgeted dom k a u₀ u₁ (L ((directionZeroSet u₁).card))) ∧
        (∀ z : ℕ, z < a → L z * ((n - z) / (a - z)) ≤ Bfar) ∧
        (∀ u₀ e₁ : Fin n → F, a ≤ (directionZeroSet e₁).card →
          (Finset.univ.filter (fun γ : F =>
            mcaEvent (F := F)
              ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ e₁ γ)).card
            ≤ Bnear) ∧
        ((max Bfar Bnear : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar ∧
        δ ≤ 1) := by
  rintro ⟨hfarL, hfit, hlow, hBudget, hδ1⟩
  exact hfail
    (mcaDeltaStar_ge_of_farLineListBudgeted_zeroStratified dom k a δ εstar L haC haF
      hfarL hfit hlow hBudget hδ1)

open Classical in
/-- Deep support-aware obstruction: a failed `δ*` floor rules out the z-stratified far branch
plus low-profile safe branch plus unsafe large-zero branch package. -/
theorem not_zeroStratified_lowProfileFiber_package_of_mcaDeltaStar_floor_failure
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar Bsafe Bunsafe : ℕ} (L M : ℕ → ℕ)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfail :
      ¬ δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar) :
    ¬ ((∀ u₀ u₁ : Fin n → F,
          FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
            LineListBudgeted dom k a u₀ u₁ (L ((directionZeroSet u₁).card))) ∧
        (∀ z : ℕ, z < a → L z * ((n - z) / (a - z)) ≤ Bfar) ∧
        (∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
          ZeroDirectionSafeLine dom k a u₀ u₁ →
            ∀ t : ℕ, t < a → t < k → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
              (coordinateAgreementFiber dom k u₀ S).card ≤ M t) ∧
        UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n)
          a Bsafe (fun t => if t < k then M t else 1) ∧
        (∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
          (Finset.univ.filter (fun γ : F =>
            mcaEvent (F := F)
              ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
            ≤ Bunsafe) ∧
        ((max Bfar (max Bsafe Bunsafe) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar ∧
        δ ≤ 1) := by
  rintro ⟨hfarL, hfit, hlowFiber, hsafeFit, hunsafe, hBudget, hδ1⟩
  exact hfail
    (mcaDeltaStar_ge_of_zeroStratified_lowProfileFibers dom hk a δ εstar L M haC haF
      hfarL hfit hlowFiber hsafeFit hunsafe hBudget hδ1)

end ProximityGap.LineListMCAWeld.SupportAware.Frontier.R113SupportAwareWeldObstructions

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LineListMCAWeld.SupportAware.Frontier.R113SupportAwareWeldObstructions.not_zeroStratified_weld_package_of_mcaDeltaStar_floor_failure
#print axioms
  ProximityGap.LineListMCAWeld.SupportAware.Frontier.R113SupportAwareWeldObstructions.not_zeroStratified_lowProfileFiber_package_of_mcaDeltaStar_floor_failure
