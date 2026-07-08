/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R158PuncturedListBudgetGuards

/-!
# LANE W6 (#466 round 159): capped-budget consumer for the punctured-list socket

R157 exposes the positive punctured-list weld with an exact nested budget
`max Bfar (max (Bpunctured * n) Bunsafe)`.  R158 proves basic guards and non-vacuity.

This file packages the consumer in the form a production proof usually wants: prove the three branch
budgets at convenient local levels, show their combined maximum fits under one external cap `Bcap`,
and spend `Bcap / q` against `εstar`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LineListMCAWeld.SupportAware.Frontier.R159PuncturedListBudgetCapConsumer

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.FarCosetExplosion
open ProximityGap.LineListMCAWeld
open ProximityGap.LineListMCAWeld.SupportAware
open ProximityGap.LowProfileCoupled
open ProximityGap.LineListMCAWeld.SupportAware.Frontier.R157PuncturedListBudgetConsumer
open ProximityGap.LineListMCAWeld.SupportAware.Frontier.R158PuncturedListBudgetGuards

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The exact nested R157 budget can be paid through any larger single natural cap. -/
theorem puncturedList_nestedBudget_le_cap
    {Bfar Bpunctured Bunsafe Bcap : ℕ}
    (hcap : max Bfar (max (Bpunctured * n) Bunsafe) ≤ Bcap) :
    ((max Bfar (max (Bpunctured * n) Bunsafe) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞)
      ≤ (Bcap : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  ENNReal.div_le_div_right (by exact_mod_cast hcap) _

open Classical in
/-- Single-cap form of the R157 punctured-list weld consumer. -/
theorem mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget_cap
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar Bpunctured Bunsafe Bcap : ℕ} (L : ℕ → ℕ)
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
    (hcap : max Bfar (max (Bpunctured * n) Bunsafe) ≤ Bcap)
    (hBudget : (Bcap : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget dom k a δ εstar L haC haF
    hfarL hfit hpunctured hunsafe
    (le_trans (puncturedList_nestedBudget_le_cap (F := F) (n := n) hcap) hBudget) hδ1

open Classical in
/-- Monotone single-cap form: local proofs may land below relaxed branch budgets, and the relaxed
branch maximum is what gets paid through `Bcap`. -/
theorem mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget_cap_mono
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar₀ Bpunctured₀ Bunsafe₀ Bfar Bpunctured Bunsafe Bcap : ℕ} (L : ℕ → ℕ)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : ∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁ (L ((directionZeroSet u₁).card)))
    (hfit₀ : ∀ z : ℕ, z < a → L z * ((n - z) / (a - z)) ≤ Bfar₀)
    (hpunctured₀ : PuncturedListBudget dom k a Bpunctured₀)
    (hunsafe₀ : ∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ Bunsafe₀)
    (hBfar : Bfar₀ ≤ Bfar)
    (hBpunctured : Bpunctured₀ ≤ Bpunctured)
    (hBunsafe : Bunsafe₀ ≤ Bunsafe)
    (hcap : max Bfar (max (Bpunctured * n) Bunsafe) ≤ Bcap)
    (hBudget : (Bcap : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar := by
  exact mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget_cap dom k a δ εstar L
    haC haF hfarL
    (fun z hz => le_trans (hfit₀ z hz) hBfar)
    (puncturedListBudget_mono dom k a hBpunctured hpunctured₀)
    (fun u₀ u₁ hnot => le_trans (hunsafe₀ u₀ u₁ hnot) hBunsafe)
    hcap hBudget hδ1

end ProximityGap.LineListMCAWeld.SupportAware.Frontier.R159PuncturedListBudgetCapConsumer

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LineListMCAWeld.SupportAware.Frontier.R159PuncturedListBudgetCapConsumer.puncturedList_nestedBudget_le_cap
#print axioms
  ProximityGap.LineListMCAWeld.SupportAware.Frontier.R159PuncturedListBudgetCapConsumer.mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget_cap
#print axioms
  ProximityGap.LineListMCAWeld.SupportAware.Frontier.R159PuncturedListBudgetCapConsumer.mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget_cap_mono
