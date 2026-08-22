/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListArithmeticObstruction
import ArkLib.Data.CodingTheory.ProximityGap.LineListSingletonDefectGeometry

/-!
# Arithmetic obstruction for the raw singleton-profile envelope

`LineListSingletonDefectGeometry.lean` packages a positive control route: if the exact singleton
profile envelope `D t` dominates the raw weighted MDS term
`|F|^(k-t) * support/(a-t)`, then the exact singleton-profile interface can consume it.  This file
records the matching arithmetic obstruction.  The combined
`puncturedWeight + singletonProfile <= 2B` budget contains every individual raw weighted summand,
so in the common `2a <= n` range the raw singleton route cannot fit any `B` with
`2B < |F|^k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The combined exact singleton-profile budget contains every raw weighted MDS singleton term
whose profile envelope `D` dominates that raw term. -/
theorem rawFieldPowSingletonProfileBudget_term_le
    (dom : Fin n ↪ F) (k a B : ℕ) (D : ℕ → ℕ)
    (u₀ u₁ : Fin n → F) {t : ℕ} (ht : t < a)
    (hnotEligible : ¬ SupportEligibleLineDirection a u₁)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hRaw : Fintype.card F ^ (k - t) * ((directionSupportSet u₁).card / (a - t)) ≤ D t)
    (hbudget : UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D) :
    (directionZeroSet u₁).card.choose t *
        (Fintype.card F ^ (k - t) * ((directionSupportSet u₁).card / (a - t))) ≤
      2 * B := by
  have hmem : t ∈ Finset.range a := Finset.mem_range.mpr ht
  have hrawD :
      (directionZeroSet u₁).card.choose t *
          (Fintype.card F ^ (k - t) * ((directionSupportSet u₁).card / (a - t)))
        ≤ (directionZeroSet u₁).card.choose t * D t :=
    Nat.mul_le_mul_left _ hRaw
  have hterm :
      (directionZeroSet u₁).card.choose t * D t
        ≤ ∑ t ∈ Finset.range a, (directionZeroSet u₁).card.choose t * D t := by
    exact Finset.single_le_sum
      (f := fun t => (directionZeroSet u₁).card.choose t * D t)
      (fun _ _ => Nat.zero_le _) hmem
  have hsum :
      ∑ t ∈ Finset.range a, (directionZeroSet u₁).card.choose t * D t
        ≤ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
          + ∑ t ∈ Finset.range a, (directionZeroSet u₁).card.choose t * D t :=
    Nat.le_add_left _ _
  exact le_trans hrawD (le_trans hterm (le_trans hsum
    (hbudget u₀ u₁ hnotEligible hsafe)))

/-- One large raw weighted MDS singleton summand refutes the combined exact singleton-profile
budget, provided `D` is at least that raw envelope on the large-zero safe branch. -/
theorem not_uniformWeightPlusExactSingletonProfileBudgeted_of_rawFieldPow_term_gt
    (dom : Fin n ↪ F) (k a B : ℕ) (D : ℕ → ℕ)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hRaw : ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      ∀ t : ℕ, t < a →
        Fintype.card F ^ (k - t) * ((directionSupportSet u₁).card / (a - t)) ≤ D t)
    (hgt : ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ∃ t : ℕ, t < a ∧
        2 * B <
          (directionZeroSet u₁).card.choose t *
            (Fintype.card F ^ (k - t) *
              ((directionSupportSet u₁).card / (a - t)))) :
    ¬ UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D := by
  intro hbudget
  rcases hgt with ⟨u₁, hnotEligible, t, ht, hgt⟩
  let u₀ : Fin n → F := fun _ => 0
  exact (not_lt_of_ge
    (rawFieldPowSingletonProfileBudget_term_le
      (F := F) (n := n) dom k a B D u₀ u₁ ht hnotEligible
      (hZeroSafe u₀ u₁) (hRaw u₁ hnotEligible t ht) hbudget)) hgt

open Classical in
/-- In the common range `2a <= n`, the raw singleton arithmetic obstruction has an explicit
`t = 0` witness: a large-zero direction whose weighted raw summand is already above `2B` whenever
`2B < |F|^k`. -/
theorem exists_rawFieldPowSingletonProfileBudget_term_gt_of_two_mul_le
    (k a B : ℕ) (ha : 0 < a) (h2a : 2 * a ≤ n)
    (hB : 2 * B < Fintype.card F ^ k) :
    ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ∃ t : ℕ, t < a ∧
        2 * B <
          (directionZeroSet u₁).card.choose t *
            (Fintype.card F ^ (k - t) *
              ((directionSupportSet u₁).card / (a - t))) := by
  rcases exists_largeZero_direction_support_ge_of_two_mul_le (F := F) (n := n) a h2a with
    ⟨u₁, hnotEligible, hsupport⟩
  refine ⟨u₁, hnotEligible, 0, ha, ?_⟩
  have hdiv : 1 ≤ (directionSupportSet u₁).card / a := Nat.div_pos hsupport ha
  have hpow_le :
      Fintype.card F ^ k ≤
        Fintype.card F ^ k * ((directionSupportSet u₁).card / a) :=
    Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.zero_lt_one hdiv)
  exact lt_of_lt_of_le hB (by simpa using hpow_le)

open Classical in
/-- In the common range `2a <= n`, the raw weighted MDS singleton-profile envelope cannot fit a
combined exact singleton-profile target with `2B < |F|^k`, assuming zero-direction safety and that
`D` dominates the raw envelope on large-zero directions. -/
theorem not_uniformWeightPlusExactSingletonProfileBudgeted_rawFieldPow_of_two_mul_le
    (dom : Fin n ↪ F) (k a B : ℕ) (D : ℕ → ℕ)
    (ha : 0 < a) (h2a : 2 * a ≤ n)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hRaw : ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      ∀ t : ℕ, t < a →
        Fintype.card F ^ (k - t) * ((directionSupportSet u₁).card / (a - t)) ≤ D t)
    (hB : 2 * B < Fintype.card F ^ k) :
    ¬ UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D := by
  exact not_uniformWeightPlusExactSingletonProfileBudgeted_of_rawFieldPow_term_gt
    (F := F) (n := n) dom k a B D hZeroSafe hRaw
    (exists_rawFieldPowSingletonProfileBudget_term_gt_of_two_mul_le
      (F := F) (n := n) k a B ha h2a hB)

open Classical in
/-- The split low-raw/high-support singleton route already pays the raw field-power cost at
profile `t = 0`: in the common range `2a <= n`, any combined exact singleton-profile budget whose
low profiles dominate the raw weighted MDS term forces `|F|^k <= 2B`. -/
theorem fieldPow_le_two_mul_of_lowRawSingletonBudget
    (dom : Fin n ↪ F) (k a B : ℕ) (D : ℕ → ℕ)
    (hk : 0 < k) (ha : 0 < a) (h2a : 2 * a ≤ n)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hLow : ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      ∀ t : ℕ, t < a → t < k →
        Fintype.card F ^ (k - t) * ((directionSupportSet u₁).card / (a - t)) ≤ D t)
    (hbudget : UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D) :
    Fintype.card F ^ k ≤ 2 * B := by
  rcases exists_largeZero_direction_support_ge_of_two_mul_le (F := F) (n := n) a h2a with
    ⟨u₁, hnotEligible, hsupport⟩
  let u₀ : Fin n → F := fun _ => 0
  have hterm :
      (directionZeroSet u₁).card.choose 0 *
          (Fintype.card F ^ (k - 0) * ((directionSupportSet u₁).card / (a - 0))) ≤
        2 * B :=
    rawFieldPowSingletonProfileBudget_term_le
      (F := F) (n := n) dom k a B D u₀ u₁ ha hnotEligible
      (hZeroSafe u₀ u₁) (hLow u₁ hnotEligible 0 ha hk) hbudget
  have hdiv : 1 ≤ (directionSupportSet u₁).card / a := Nat.div_pos hsupport ha
  have hpow_le :
      Fintype.card F ^ k ≤
        Fintype.card F ^ k * ((directionSupportSet u₁).card / a) :=
    Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.zero_lt_one hdiv)
  exact le_trans (by simpa [Nat.choose_zero_right] using hpow_le) hterm

open Classical in
/-- Consequently, the split low-raw/high-support singleton certificate cannot fit a production
target below `|F|^k / 2` in the common `2a <= n`, `0 < k` range.  The high-profile support-only
side is irrelevant to this obstruction: `t = 0` already lies on the low side. -/
theorem not_uniformWeightPlusExactSingletonProfileBudgeted_lowRaw_of_two_mul_le
    (dom : Fin n ↪ F) (k a B : ℕ) (D : ℕ → ℕ)
    (hk : 0 < k) (ha : 0 < a) (h2a : 2 * a ≤ n)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hLow : ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      ∀ t : ℕ, t < a → t < k →
        Fintype.card F ^ (k - t) * ((directionSupportSet u₁).card / (a - t)) ≤ D t)
    (hB : 2 * B < Fintype.card F ^ k) :
    ¬ UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D := by
  intro hbudget
  exact (not_lt_of_ge
    (fieldPow_le_two_mul_of_lowRawSingletonBudget
      (F := F) (n := n) dom k a B D hk ha h2a hZeroSafe hLow hbudget)) hB

open Classical in
/-- Full scanner-facing raw singleton obstruction.  In the common range `2a <= n`, raw dominance
and `2B < |F|^k` force either zero-direction saturation or failure of the combined exact
singleton-profile budget. -/
theorem unsafe_or_not_uniformWeightPlusExactSingletonProfileBudgeted_rawFieldPow_of_two_mul_le
    (dom : Fin n ↪ F) (k a B : ℕ) (D : ℕ → ℕ)
    (ha : 0 < a) (h2a : 2 * a ≤ n)
    (hRaw : ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      ∀ t : ℕ, t < a →
        Fintype.card F ^ (k - t) * ((directionSupportSet u₁).card / (a - t)) ≤ D t)
    (hB : 2 * B < Fintype.card F ^ k) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      ¬ UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D := by
  by_cases hZeroSafe : UniformZeroDirectionSafe dom k a
  · exact Or.inr
      (not_uniformWeightPlusExactSingletonProfileBudgeted_rawFieldPow_of_two_mul_le
        (F := F) (n := n) dom k a B D ha h2a hZeroSafe hRaw hB)
  · exact Or.inl
      ((not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
        dom k a).mp hZeroSafe)

section SourceAudit

#print axioms rawFieldPowSingletonProfileBudget_term_le
#print axioms not_uniformWeightPlusExactSingletonProfileBudgeted_of_rawFieldPow_term_gt
#print axioms exists_rawFieldPowSingletonProfileBudget_term_gt_of_two_mul_le
#print axioms not_uniformWeightPlusExactSingletonProfileBudgeted_rawFieldPow_of_two_mul_le
#print axioms fieldPow_le_two_mul_of_lowRawSingletonBudget
#print axioms not_uniformWeightPlusExactSingletonProfileBudgeted_lowRaw_of_two_mul_le
#print axioms unsafe_or_not_uniformWeightPlusExactSingletonProfileBudgeted_rawFieldPow_of_two_mul_le

end SourceAudit

end ProximityGap.Ownership
