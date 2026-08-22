/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListMCAWeld

/-!
# Obstructions for the prize-facing line-list weld

`LineListMCAWeld.lean` gives the positive production interface: far-line list budgets plus
large-zero budgets imply the `mcaDeltaStar` floor.  This file records the matching
audit-facing contrapositives.  If the floor fails after the threshold/budget arithmetic is fixed,
then the corresponding production package cannot have been simultaneously true.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LineListMCAWeld.Frontier.R112LineListWeldObstructions

open ProximityGap.LineListMCAWeld
open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.FarCosetExplosion

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Root weld obstruction: if the `δ*` floor fails, then the far-line list budget, arithmetic
fit, large-zero branch budget, normalized budget, and radius side condition cannot all hold. -/
theorem not_farLineList_weld_package_of_mcaDeltaStar_floor_failure
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞) {L Bfar Bnear : ℕ}
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfail :
      ¬ δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar) :
    ¬ ((∀ u₀ u₁ : Fin n → F,
          FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
            LineListBudgeted dom k a u₀ u₁ L) ∧
        (∀ z : ℕ, z < a → L * ((n - z) / (a - z)) ≤ Bfar) ∧
        (∀ u₀ e₁ : Fin n → F, a ≤ (directionZeroSet e₁).card →
          (Finset.univ.filter (fun γ : F =>
            mcaEvent (F := F)
              ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ e₁ γ)).card
            ≤ Bnear) ∧
        ((max Bfar Bnear : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar ∧
        δ ≤ 1) := by
  rintro ⟨hfarL, hfit, hlow, hBudget, hδ1⟩
  exact hfail
    (mcaDeltaStar_ge_of_farLineListBudgeted dom k a δ εstar haC haF
      hfarL hfit hlow hBudget hδ1)

open Classical in
/-- Split large-zero obstruction: a failed `δ*` floor rules out the simultaneous far,
safe-large-zero, unsafe-large-zero, and budget package. -/
theorem not_largeZeroSplit_weld_package_of_mcaDeltaStar_floor_failure
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {L Bfar Bsafe Bunsafe : ℕ}
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfail :
      ¬ δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar) :
    ¬ ((∀ u₀ u₁ : Fin n → F,
          FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
            LineListBudgeted dom k a u₀ u₁ L) ∧
        (∀ z : ℕ, z < a → L * ((n - z) / (a - z)) ≤ Bfar) ∧
        LargeZeroSafeLineBadScalarsBudgeted dom k a Bsafe ∧
        (∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
          (Finset.univ.filter (fun γ : F =>
            mcaEvent (F := F)
              ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
            ≤ Bunsafe) ∧
        ((max Bfar (max Bsafe Bunsafe) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar ∧
        δ ≤ 1) := by
  rintro ⟨hfarL, hfit, hsafe, hunsafe, hBudget, hδ1⟩
  exact hfail
    (mcaDeltaStar_ge_of_farLineListBudgeted_largeZeroSplit dom k a δ εstar haC haF
      hfarL hfit hsafe hunsafe hBudget hδ1)

open Classical in
/-- Low-profile fiber obstruction: once the high fibers have been discharged by uniqueness,
a failed `δ*` floor rules out the far-line budget plus low-profile fiber package. -/
theorem not_lowProfileFiber_weld_package_of_mcaDeltaStar_floor_failure
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {L Bfar Bsafe Bunsafe : ℕ} (M : ℕ → ℕ)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfail :
      ¬ δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar) :
    ¬ ((∀ u₀ u₁ : Fin n → F,
          FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
            LineListBudgeted dom k a u₀ u₁ L) ∧
        (∀ z : ℕ, z < a → L * ((n - z) / (a - z)) ≤ Bfar) ∧
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
    (mcaDeltaStar_ge_of_farLineListBudgeted_lowProfileFibers dom hk a δ εstar M haC haF
      hfarL hfit hlowFiber hsafeFit hunsafe hBudget hδ1)

end ProximityGap.LineListMCAWeld.Frontier.R112LineListWeldObstructions

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LineListMCAWeld.Frontier.R112LineListWeldObstructions.not_farLineList_weld_package_of_mcaDeltaStar_floor_failure
#print axioms
  ProximityGap.LineListMCAWeld.Frontier.R112LineListWeldObstructions.not_largeZeroSplit_weld_package_of_mcaDeltaStar_floor_failure
#print axioms
  ProximityGap.LineListMCAWeld.Frontier.R112LineListWeldObstructions.not_lowProfileFiber_weld_package_of_mcaDeltaStar_floor_failure
