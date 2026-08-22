/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R165PuncturedUniqueArithmeticWitness

/-!
# LANE HLOW (#466 round 166): numeric closure of the punctured-unique slice

R165 extracts the failed punctured-unique consumer into zero/support counts `z,s` with
`z + s = n`, `a ≤ z`, and strict failure of `z + k ≤ 2 * (a - s)`.

This file records the matching parameter-only positive region.  If `2n + k ≤ 3a`, then every
large-zero direction automatically lies in the punctured unique-decoding band.  This is the
`t = 0` analogue of the support-localized threshold `n + k + t ≤ 3a` in
`_LowProfileFiberBound.lean`, and gives a direct numeric consumer for R160.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.FarCosetExplosion
open ProximityGap.LineListMCAWeld
open ProximityGap.LineListMCAWeld.SupportAware
open ProximityGap.LargeZeroWitnessSplit.Frontier.R160PuncturedUniqueBudgetConsumer
open ProximityGap.LargeZeroWitnessSplit.Frontier.R165PuncturedUniqueArithmeticWitness

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Under the numeric threshold `2n + k ≤ 3a`, every large-zero direction satisfies the
punctured unique-decoding inequality. -/
theorem punctured_unique_of_two_mul_n_add_k_le_three_mul_a
    {a k : ℕ} (u₁ : Fin n → F)
    (hnotEligible : ¬ SupportEligibleLineDirection a u₁)
    (h3 : 2 * n + k ≤ 3 * a) :
    (directionZeroSet u₁).card + k ≤
      2 * (a - (directionSupportSet u₁).card) := by
  have hz : a ≤ (directionZeroSet u₁).card :=
    zero_card_ge_of_not_supportEligible hnotEligible
  have hsum : (directionZeroSet u₁).card + (directionSupportSet u₁).card = n := by
    rw [directionZeroSet, directionSupportSet,
      Finset.card_filter_add_card_filter_not]
    simp
  omega

/-- Numeric uniform form: the threshold `2n + k ≤ 3a` supplies the R160 uniform
punctured-unique hypothesis. -/
theorem uniform_punctured_unique_of_two_mul_n_add_k_le_three_mul_a
    {a k : ℕ} (h3 : 2 * n + k ≤ 3 * a) :
    ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      (directionZeroSet u₁).card + k ≤
        2 * (a - (directionSupportSet u₁).card) :=
  fun u₁ hnotEligible =>
    punctured_unique_of_two_mul_n_add_k_le_three_mul_a u₁ hnotEligible h3

/-- The R165 arithmetic obstruction cannot occur in the numeric unique-decoding region. -/
theorem not_exists_zero_support_counts_punctured_unique_arithmetic_obstruction
    {a k : ℕ} (h3 : 2 * n + k ≤ 3 * a) :
    ¬ ∃ z s : ℕ, z + s = n ∧ a ≤ z ∧ 2 * (a - s) < z + k := by
  rintro ⟨z, s, hsum, hz, hstrict⟩
  omega

/-- The threshold is sharp at the count level: if `3a < 2n + k`, then the profile
`z = a`, `s = n - a` already gives the R165 arithmetic obstruction. -/
theorem exists_zero_support_counts_punctured_unique_arithmetic_obstruction_of_three_mul_a_lt
    {a k : ℕ} (han : a ≤ n) (hlt : 3 * a < 2 * n + k) :
    ∃ z s : ℕ, z + s = n ∧ a ≤ z ∧ 2 * (a - s) < z + k := by
  by_cases hpos : 0 < a + k
  · refine ⟨a, n - a, ?_, le_rfl, ?_⟩
    · omega
    · by_cases hs : n - a ≤ a
      · omega
      · omega
  · have ha0 : a = 0 := by omega
    have hk0 : k = 0 := by omega
    refine ⟨n, 0, by omega, by omega, ?_⟩
    have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    omega

/-- Exact numeric characterization of the R165 count obstruction.  In the natural range
`a ≤ n`, no zero/support-count obstruction exists iff `2n + k ≤ 3a`. -/
theorem not_exists_zero_support_counts_punctured_unique_arithmetic_obstruction_iff
    {a k : ℕ} (han : a ≤ n) :
    (¬ ∃ z s : ℕ, z + s = n ∧ a ≤ z ∧ 2 * (a - s) < z + k) ↔
      2 * n + k ≤ 3 * a := by
  constructor
  · intro hnot
    by_contra hle
    have hlt : 3 * a < 2 * n + k := Nat.lt_of_not_ge hle
    exact hnot
      (exists_zero_support_counts_punctured_unique_arithmetic_obstruction_of_three_mul_a_lt
        (n := n) han hlt)
  · exact not_exists_zero_support_counts_punctured_unique_arithmetic_obstruction (n := n)

/-- Deficit form of the positive numeric region.  If `a = n - deficit`, the condition
`2n + k ≤ 3a` is implied by `3 * deficit + k ≤ n`. -/
theorem two_mul_n_add_k_le_three_mul_a_of_deficit_region
    {a k : ℕ} (han : a ≤ n) (hdef : 3 * (n - a) + k ≤ n) :
    2 * n + k ≤ 3 * a := by
  omega

open Classical in
/-- With the R160 side hypotheses fixed, any failure of the MCA-threshold conclusion must occur
outside the numeric punctured-unique region.  Equivalently, the R165 witness forces
`3a < 2n + k`. -/
theorem three_mul_a_lt_two_mul_n_add_k_of_not_mcaDeltaStar
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
    3 * a < 2 * n + k := by
  have hwit :
      ∃ z s : ℕ, z + s = n ∧ a ≤ z ∧ 2 * (a - s) < z + k :=
    exists_zero_support_counts_punctured_unique_arithmetic_obstruction_of_not_mcaDeltaStar
      dom hk a δ εstar L haC haF hfarL hfit hunsafe hcap hBudget hδ1 hfail
  by_contra hnot
  have hle : 2 * n + k ≤ 3 * a := Nat.le_of_not_gt hnot
  exact
    (not_exists_zero_support_counts_punctured_unique_arithmetic_obstruction (n := n) hle) hwit

open Classical in
/-- Deficit form of the R166 obstruction: under the same side hypotheses, a failed MCA-threshold
conclusion must lie beyond the one-third deficit region, i.e. `n < 3 * (n - a) + k`. -/
theorem n_lt_three_mul_deficit_add_k_of_not_mcaDeltaStar
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
  have hlt : 3 * a < 2 * n + k :=
    three_mul_a_lt_two_mul_n_add_k_of_not_mcaDeltaStar
      dom hk a δ εstar L haC haF hfarL hfit hunsafe hcap hBudget hδ1 hfail
  omega

open Classical in
/-- Numeric single-cap MCA-threshold consumer for the punctured unique-decoding region.  The
large-zero-safe branch spends only `n`; the only new input compared to R160 is the parameter
inequality `2n + k ≤ 3a`. -/
theorem mcaDeltaStar_ge_of_zeroStratified_puncturedUnique_numeric_cap
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {Bfar Bunsafe Bcap : ℕ} (L : ℕ → ℕ)
    (h3 : 2 * n + k ≤ 3 * a)
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
  mcaDeltaStar_ge_of_zeroStratified_puncturedUnique_cap dom hk a δ εstar L
    haC haF hfarL hfit
    (uniform_punctured_unique_of_two_mul_n_add_k_le_three_mul_a (F := F) (n := n) h3)
    hunsafe hcap hBudget hδ1

open Classical in
/-- Deficit-form numeric MCA-threshold consumer.  This is the same R166 cap theorem with the
region written as `3 * (n - a) + k ≤ n`, the natural one-third-radius form when `a` is the
agreement threshold. -/
theorem mcaDeltaStar_ge_of_zeroStratified_puncturedUnique_deficit_cap
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
  mcaDeltaStar_ge_of_zeroStratified_puncturedUnique_numeric_cap dom hk a δ εstar L
    (two_mul_n_add_k_le_three_mul_a_of_deficit_region (n := n) han hdef)
    haC haF hfarL hfit hunsafe hcap hBudget hδ1

end ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure.punctured_unique_of_two_mul_n_add_k_le_three_mul_a
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure.uniform_punctured_unique_of_two_mul_n_add_k_le_three_mul_a
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure.not_exists_zero_support_counts_punctured_unique_arithmetic_obstruction
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure.exists_zero_support_counts_punctured_unique_arithmetic_obstruction_of_three_mul_a_lt
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure.not_exists_zero_support_counts_punctured_unique_arithmetic_obstruction_iff
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure.two_mul_n_add_k_le_three_mul_a_of_deficit_region
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure.three_mul_a_lt_two_mul_n_add_k_of_not_mcaDeltaStar
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure.n_lt_three_mul_deficit_add_k_of_not_mcaDeltaStar
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure.mcaDeltaStar_ge_of_zeroStratified_puncturedUnique_numeric_cap
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R166PuncturedUniqueNumericClosure.mcaDeltaStar_ge_of_zeroStratified_puncturedUnique_deficit_cap
