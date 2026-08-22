/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R164PuncturedUniqueConsumerWitness

/-!
# LANE HLOW (#466 round 165): arithmetic form of the punctured-unique witness

R164 produces a concrete direction when the punctured-unique consumer conclusion fails.  This file
normalizes that witness into the arithmetic inequalities used by the support/zero-set obstruction
files: the direction is genuinely large-zero, the punctured inequality fails strictly, and the
support count is the complement of the zero count.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LargeZeroWitnessSplit.Frontier.R165PuncturedUniqueArithmeticWitness

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.FarCosetExplosion
open ProximityGap.LineListMCAWeld
open ProximityGap.LineListMCAWeld.SupportAware
open ProximityGap.LargeZeroWitnessSplit.Frontier.R164PuncturedUniqueConsumerWitness

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- A direction outside the support-eligible branch has at least `a` zero coordinates. -/
theorem zero_card_ge_of_not_supportEligible
    {a : ℕ} {u₁ : Fin n → F} (hnot : ¬ SupportEligibleLineDirection a u₁) :
    a ≤ (directionZeroSet u₁).card := by
  rw [SupportEligibleLineDirection] at hnot
  exact Nat.le_of_not_gt hnot

/-- Failure of the punctured unique-decoding inequality is equivalently a strict overrun. -/
theorem punctured_unique_failure_strict
    {a k : ℕ} {u₁ : Fin n → F}
    (hbad : ¬ (directionZeroSet u₁).card + k ≤
      2 * (a - (directionSupportSet u₁).card)) :
    2 * (a - (directionSupportSet u₁).card) <
      (directionZeroSet u₁).card + k := by
  exact Nat.lt_of_not_ge hbad

open Classical in
/-- Consumer failure yields a concrete large-zero direction with the strict arithmetic obstruction
and the zero/support partition recorded explicitly. -/
theorem exists_direction_punctured_unique_arithmetic_obstruction_of_not_mcaDeltaStar
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
    ∃ u₁ : Fin n → F,
      ¬ SupportEligibleLineDirection a u₁ ∧
      a ≤ (directionZeroSet u₁).card ∧
      2 * (a - (directionSupportSet u₁).card) <
        (directionZeroSet u₁).card + k ∧
      (directionSupportSet u₁).card = n - (directionZeroSet u₁).card := by
  rcases exists_direction_not_punctured_unique_of_not_mcaDeltaStar
      dom hk a δ εstar L haC haF hfarL hfit hunsafe hcap hBudget hδ1 hfail with
    ⟨u₁, hnotEligible, hbad⟩
  exact ⟨u₁, hnotEligible, zero_card_ge_of_not_supportEligible hnotEligible,
    punctured_unique_failure_strict hbad, directionSupportSet_card_eq u₁⟩

open Classical in
/-- A purely numeric socket extracted from the failed consumer: there are zero/support counts
`z,s` partitioning `n`, with `z` in the large-zero branch and violating the punctured band. -/
theorem exists_zero_support_counts_punctured_unique_arithmetic_obstruction_of_not_mcaDeltaStar
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
    ∃ z s : ℕ, z + s = n ∧ a ≤ z ∧ 2 * (a - s) < z + k := by
  rcases exists_direction_punctured_unique_arithmetic_obstruction_of_not_mcaDeltaStar
      dom hk a δ εstar L haC haF hfarL hfit hunsafe hcap hBudget hδ1 hfail with
    ⟨u₁, _hnotEligible, hzlarge, hstrict, hsupp⟩
  refine ⟨(directionZeroSet u₁).card, (directionSupportSet u₁).card, ?_, hzlarge, hstrict⟩
  rw [hsupp]
  exact Nat.add_sub_of_le (by simpa using Finset.card_le_univ (directionZeroSet u₁))

end ProximityGap.LargeZeroWitnessSplit.Frontier.R165PuncturedUniqueArithmeticWitness

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R165PuncturedUniqueArithmeticWitness.zero_card_ge_of_not_supportEligible
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R165PuncturedUniqueArithmeticWitness.punctured_unique_failure_strict
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R165PuncturedUniqueArithmeticWitness.exists_direction_punctured_unique_arithmetic_obstruction_of_not_mcaDeltaStar
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R165PuncturedUniqueArithmeticWitness.exists_zero_support_counts_punctured_unique_arithmetic_obstruction_of_not_mcaDeltaStar
