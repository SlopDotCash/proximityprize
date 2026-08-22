/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R162LargeZeroSafeUniqueFailureScanner
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R166PuncturedUniqueNumericClosure
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R2B_LargeZeroWitnessSplit

/-!
# LANE HLOW (#466 round 167): safe-branch deficit scanner

R166 closes the punctured-unique slice in the numeric region `2n + k ≤ 3a`, equivalently in
deficit form `3 * (n - a) + k ≤ n`.  This file records the branch-local consequence: the
large-zero-safe branch has budget `n` throughout that region, and any failure of that branch alone
already forces the same one-third obstruction.

This avoids carrying the full MCA-threshold consumer when the next lane only needs to reason about
the safe large-zero branch.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.FarCosetExplosion
open ProximityGap.LineListMCAWeld
open ProximityGap.LineListMCAWeld.SupportAware
open ProximityGap.LowProfileCoupled
open ProximityGap.LargeZeroWitnessSplit
open ProximityGap.LargeZeroWitnessSplit.Frontier.R160PuncturedUniqueBudgetConsumer
open ProximityGap.LargeZeroWitnessSplit.Frontier.R162LargeZeroSafeUniqueFailureScanner
open ProximityGap.LargeZeroWitnessSplit.Frontier.R165PuncturedUniqueArithmeticWitness
open ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Numeric safe-branch consequence: in the R166 region `2n + k ≤ 3a`, the weld-facing
large-zero-safe budget is `n`. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_two_mul_n_add_k_le_three_mul_a
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (h3 : 2 * n + k ≤ 3 * a) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a n :=
  largeZeroSafeLineBadScalarsBudgeted_of_uniform_punctured_unique dom hk a
    (uniform_punctured_unique_of_two_mul_n_add_k_le_three_mul_a (F := F) (n := n) h3)

open Classical in
/-- Branch-local obstruction: if the safe large-zero budget `n` fails, the parameters must be
outside the R166 numeric region. -/
theorem three_mul_a_lt_two_mul_n_add_k_of_not_largeZeroSafe_budget_n
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (hnot : ¬ LargeZeroSafeLineBadScalarsBudgeted dom k a n) :
    3 * a < 2 * n + k := by
  rcases exists_not_punctured_unique_of_not_largeZeroSafe_budget_n dom hk a hnot with
    ⟨_u₀, u₁, hnotEligible, _hsafe, _hgt, hbad⟩
  have hz : a ≤ (directionZeroSet u₁).card :=
    zero_card_ge_of_not_supportEligible hnotEligible
  have hstrict :
      2 * (a - (directionSupportSet u₁).card) <
        (directionZeroSet u₁).card + k :=
    punctured_unique_failure_strict hbad
  have hsum : (directionZeroSet u₁).card + (directionSupportSet u₁).card = n := by
    rw [directionZeroSet, directionSupportSet,
      Finset.card_filter_add_card_filter_not]
    simp
  omega

open Classical in
/-- Deficit form of the branch-local obstruction.  If the safe branch fails and `a ≤ n`, the
deficit must be beyond one third: `n < 3 * (n - a) + k`. -/
theorem n_lt_three_mul_deficit_add_k_of_not_largeZeroSafe_budget_n
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (han : a ≤ n)
    (hnot : ¬ LargeZeroSafeLineBadScalarsBudgeted dom k a n) :
    n < 3 * (n - a) + k := by
  have hlt : 3 * a < 2 * n + k :=
    three_mul_a_lt_two_mul_n_add_k_of_not_largeZeroSafe_budget_n dom hk a hnot
  omega

open Classical in
/-- Deficit-region safe-branch consequence: `3 * (n - a) + k ≤ n` directly supplies the
weld-facing large-zero-safe budget `n`. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_deficit_region
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (han : a ≤ n)
    (hdef : 3 * (n - a) + k ≤ n) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a n :=
  largeZeroSafeLineBadScalarsBudgeted_of_two_mul_n_add_k_le_three_mul_a dom hk a
    (two_mul_n_add_k_le_three_mul_a_of_deficit_region (n := n) han hdef)

open Classical in
/-- In the one-third deficit region, the old R2B mid-band residual is empty: a large-zero
direction has support at most `n - a`, and `3 * (n - a) + k ≤ n` forces
`k + support ≤ a`, contradicting the mid-band premise `a < k + support`. -/
theorem midBandSafeLineBadScalarsBudgeted_zero_of_deficit_region
    (dom : Fin n ↪ F) {k : ℕ} (a : ℕ)
    (han : a ≤ n)
    (hdef : 3 * (n - a) + k ≤ n) :
    MidBandSafeLineBadScalarsBudgeted dom k a 0 := by
  intro _u₀ u₁ hnotEligible hmid _hsafe
  have hz : a ≤ (directionZeroSet u₁).card :=
    zero_card_ge_of_not_supportEligible hnotEligible
  have hsum : (directionZeroSet u₁).card + (directionSupportSet u₁).card = n := by
    rw [directionZeroSet, directionSupportSet,
      Finset.card_filter_add_card_filter_not]
    simp
  omega

open Classical in
/-- Residual-budget form of the deficit-region safe branch.  In the one-third deficit region,
large-zero-safe directions spend `n`; unsafe directions remain in the explicit `Bunsafe` branch. -/
theorem largeZeroResidualBudgeted_of_deficit_region
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0)
    {Bunsafe : ℕ}
    (han : a ≤ n)
    (hdef : 3 * (n - a) + k ≤ n)
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hunsafe : ∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ Bunsafe) :
    ∀ u₀ e₁ : Fin n → F, a ≤ (directionZeroSet e₁).card →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ e₁ γ)).card
        ≤ max n Bunsafe :=
  lowWeight_badCount_le_of_largeZeroSafe_budget dom k a δ haF
    (largeZeroSafeLineBadScalarsBudgeted_of_deficit_region dom hk a han hdef)
    hunsafe

open Classical in
/-- Zero-stratified MCA-threshold consumer with the safe branch discharged by the deficit-region
punctured-unique theorem.  The remaining explicit work is the far branch, unsafe branch, and final
single-cap arithmetic. -/
theorem mcaDeltaStar_ge_of_zeroStratified_safeDeficit_cap
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar Bunsafe Bcap : ℕ} (L : ℕ → ℕ)
    (han : a ≤ n)
    (hdef : 3 * (n - a) + k ≤ n)
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
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  mcaDeltaStar_ge_of_farLineListBudgeted_zeroStratified dom k a δ εstar L
    haC haF hfarL hfit
    (largeZeroResidualBudgeted_of_deficit_region dom hk a δ han hdef haF hunsafe)
    (le_trans
      (ENNReal.div_le_div_right (by exact_mod_cast hcap) _)
      hBudget)
    hδ1

open Classical in
/-- Failure certificate for the safe-deficit consumer.  Once the far branch, unsafe branch, cap,
and final budget are fixed, failure of the MCA-threshold conclusion forces the parameters outside
the one-third deficit region. -/
theorem n_lt_three_mul_deficit_add_k_of_not_mcaDeltaStar_safeDeficit_cap
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar Bunsafe Bcap : ℕ} (L : ℕ → ℕ)
    (han : a ≤ n)
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
    n < 3 * (n - a) + k := by
  by_contra hnot
  exact hfail
    (mcaDeltaStar_ge_of_zeroStratified_safeDeficit_cap dom hk a δ εstar L
      han (Nat.le_of_not_gt hnot) haC haF hfarL hfit hunsafe hcap hBudget hδ1)

open Classical in
/-- Same as `mcaDeltaStar_ge_of_zeroStratified_safeDeficit_cap`, with the unsafe branch discharged
by the trivial field-size cap.  In the deficit region, callers only need to prove the far branch
and pay `max Bfar (max n q)`. -/
theorem mcaDeltaStar_ge_of_zeroStratified_safeDeficit_unsafeField_cap
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar Bcap : ℕ} (L : ℕ → ℕ)
    (han : a ≤ n)
    (hdef : 3 * (n - a) + k ≤ n)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : ∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁ (L ((directionZeroSet u₁).card)))
    (hfit : ∀ z : ℕ, z < a → L z * ((n - z) / (a - z)) ≤ Bfar)
    (hcap : max Bfar (max n (Fintype.card F)) ≤ Bcap)
    (hBudget : (Bcap : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar := by
  have hunsafe : ∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ Fintype.card F := by
    intro u₀ u₁ _hnotSafe
    exact unsafe_branch_budget_satisfiable dom k δ u₀ u₁
  exact mcaDeltaStar_ge_of_zeroStratified_safeDeficit_cap dom hk a δ εstar L
    han hdef haC haF hfarL hfit hunsafe hcap hBudget hδ1

open Classical in
/-- Failure certificate for the unsafe-field specialization.  With the unsafe branch discharged
by the trivial `q` cap, any remaining failure under the far/cap/budget hypotheses forces the same
one-third deficit obstruction. -/
theorem n_lt_three_mul_deficit_add_k_of_not_mcaDeltaStar_safeDeficit_unsafeField_cap
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar Bcap : ℕ} (L : ℕ → ℕ)
    (han : a ≤ n)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : ∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁ (L ((directionZeroSet u₁).card)))
    (hfit : ∀ z : ℕ, z < a → L z * ((n - z) / (a - z)) ≤ Bfar)
    (hcap : max Bfar (max n (Fintype.card F)) ≤ Bcap)
    (hBudget : (Bcap : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1)
    (hfail : ¬ δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar) :
    n < 3 * (n - a) + k := by
  by_contra hnot
  exact hfail
    (mcaDeltaStar_ge_of_zeroStratified_safeDeficit_unsafeField_cap dom hk a δ εstar L
      han (Nat.le_of_not_gt hnot) haC haF hfarL hfit hcap hBudget hδ1)

omit [DecidableEq F] in
open Classical in
/-- Fully trivial far/unsafe instantiation of the safe-deficit consumer.  This is deliberately
not prize-sized; it certifies that after the safe branch is removed by the deficit theorem, the
remaining consumer is non-vacuous with the standard field-power far envelope and unsafe `q` cap. -/
theorem mcaDeltaStar_ge_of_zeroStratified_safeDeficit_fieldPow
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    (han : a ≤ n)
    (hdef : 3 * (n - a) + k ≤ n)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hBudget :
      ((max (Fintype.card F ^ k * n) (max n (Fintype.card F)) : ℕ) : ℝ≥0∞) /
          (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar := by
  obtain ⟨hfarL, hfit⟩ :=
    zeroStratified_far_positions_satisfiable dom k a δ
  exact mcaDeltaStar_ge_of_zeroStratified_safeDeficit_unsafeField_cap dom hk a δ εstar
    (fun _ : ℕ => Fintype.card F ^ k)
    han hdef haC haF hfarL hfit (le_refl _) hBudget hδ1

end ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner.largeZeroSafeLineBadScalarsBudgeted_of_two_mul_n_add_k_le_three_mul_a
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner.three_mul_a_lt_two_mul_n_add_k_of_not_largeZeroSafe_budget_n
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner.n_lt_three_mul_deficit_add_k_of_not_largeZeroSafe_budget_n
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner.largeZeroSafeLineBadScalarsBudgeted_of_deficit_region
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner.midBandSafeLineBadScalarsBudgeted_zero_of_deficit_region
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner.largeZeroResidualBudgeted_of_deficit_region
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner.mcaDeltaStar_ge_of_zeroStratified_safeDeficit_cap
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner.n_lt_three_mul_deficit_add_k_of_not_mcaDeltaStar_safeDeficit_cap
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner.mcaDeltaStar_ge_of_zeroStratified_safeDeficit_unsafeField_cap
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner.n_lt_three_mul_deficit_add_k_of_not_mcaDeltaStar_safeDeficit_unsafeField_cap
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R167PuncturedUniqueSafeDeficitScanner.mcaDeltaStar_ge_of_zeroStratified_safeDeficit_fieldPow
