/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R157PuncturedListBudgetConsumer

/-!
# LANE W6 (#466 round 158): guard lemmas for the punctured-list consumer

R157 rewires the large-zero-safe branch through the direct `PuncturedListBudget`.  This file records
the two sanity checks that keep that new consumer honest:

* `PuncturedListBudget` is monotone in the budget parameter.
* The hypothesis is satisfiable at the trivial field-power envelope `q^k`, so the open content is
  only the size of the budget, not consistency of the consumer.

The final theorem packages the fully trivial field-power instantiation of the R157 consumer.  It is
deliberately huge and not prize-closing; its role is to certify that the new interface is a genuine
proof socket, not a vacuous one.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LineListMCAWeld.SupportAware.Frontier.R158PuncturedListBudgetGuards

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.FarCosetExplosion
open ProximityGap.LineListMCAWeld
open ProximityGap.LineListMCAWeld.SupportAware
open ProximityGap.LowProfileCoupled
open ProximityGap.LineListMCAWeld.SupportAware.Frontier.R157PuncturedListBudgetConsumer

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- The direct punctured-list budget is monotone in its numeric budget. -/
theorem puncturedListBudget_mono
    (dom : Fin n ↪ F) (k a : ℕ) {B B' : ℕ}
    (hBB : B ≤ B') (h : PuncturedListBudget dom k a B) :
    PuncturedListBudget dom k a B' := by
  intro u₀ u₁ hne hsafe
  exact le_trans (h u₀ u₁ hne hsafe) hBB

open Classical in
/-- The punctured-list budget position is satisfiable at the trivial field-power envelope `q^k`.
This is just the usual line-list field-power cap restricted to the large-zero-safe class. -/
theorem puncturedListBudget_field_pow_k
    (dom : Fin n ↪ F) (k a : ℕ) :
    PuncturedListBudget dom k a (Fintype.card F ^ k) := by
  intro u₀ u₁ _hne _hsafe
  exact lineListBudgeted_field_pow_k dom k a u₀ u₁

/-- The R157 far and punctured budget positions are jointly satisfiable at the same field-power
envelope, with the standard `L*z` fit realized by `q^k * n`.  The unsafe branch is already
realized separately by `unsafe_branch_budget_satisfiable`. -/
theorem zeroStratified_punctured_far_positions_satisfiable
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) :
    (∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁
          ((fun _ : ℕ => Fintype.card F ^ k) ((directionZeroSet u₁).card)))
    ∧ (∀ z : ℕ, z < a →
        (fun _ : ℕ => Fintype.card F ^ k) z * ((n - z) / (a - z))
          ≤ Fintype.card F ^ k * n)
    ∧ PuncturedListBudget dom k a (Fintype.card F ^ k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u₀ u₁ _hfar
    exact lineListBudgeted_field_pow_k dom k a u₀ u₁
  · intro z hz
    exact supportAware_fit_satisfiable (n := n) a (Fintype.card F ^ k) z hz
  · exact puncturedListBudget_field_pow_k dom k a

open Classical in
/-- Fully trivial field-power instantiation of the R157 consumer.  The conclusion is intentionally
weak: it requires the enormous budget `(max (q^k*n) (max (q^k*n) q))/q` to fit below `εstar`.
Its purpose is the non-vacuity audit for the consumer shape. -/
theorem mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget_fieldPow
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hBudget :
      ((max (Fintype.card F ^ k * n)
            (max (Fintype.card F ^ k * n) (Fintype.card F)) : ℕ) : ℝ≥0∞) /
          (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar := by
  obtain ⟨hfarL, hfit, hpunctured⟩ :=
    zeroStratified_punctured_far_positions_satisfiable dom k a δ
  have hunsafe : ∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ Fintype.card F := by
    intro u₀ u₁ _hunsafe
    exact unsafe_branch_budget_satisfiable dom k δ u₀ u₁
  exact mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget dom k a δ εstar
    (fun _ : ℕ => Fintype.card F ^ k) haC haF hfarL hfit hpunctured hunsafe hBudget hδ1

end ProximityGap.LineListMCAWeld.SupportAware.Frontier.R158PuncturedListBudgetGuards

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LineListMCAWeld.SupportAware.Frontier.R158PuncturedListBudgetGuards.puncturedListBudget_mono
#print axioms
  ProximityGap.LineListMCAWeld.SupportAware.Frontier.R158PuncturedListBudgetGuards.puncturedListBudget_field_pow_k
#print axioms
  ProximityGap.LineListMCAWeld.SupportAware.Frontier.R158PuncturedListBudgetGuards.zeroStratified_punctured_far_positions_satisfiable
#print axioms
  ProximityGap.LineListMCAWeld.SupportAware.Frontier.R158PuncturedListBudgetGuards.mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget_fieldPow
