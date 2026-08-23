/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListReduction

/-!
# Arithmetic obstruction for the raw coordinate-fiber envelope

Issue #464 follow-up.  `LineListReduction.lean` proves the raw MDS coordinate-fiber envelope
`M t = |F|^(k - t)` and exposes per-`t` arithmetic obstructions to fitting that envelope into the
large-zero budget.  This file makes those obstructions parameter-visible by constructing line
directions with prescribed zero/support counts.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [Fintype F] in
/-- For every `z ≤ n`, there is a line direction with exactly `z` zero coordinates and exactly
`n - z` moving-support coordinates. -/
theorem exists_direction_zero_card_eq_support_card_eq (z : ℕ) (hz : z ≤ n) :
    ∃ u₁ : Fin n → F,
      (directionZeroSet u₁).card = z ∧ (directionSupportSet u₁).card = n - z := by
  have hz_card : z ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hz
  rcases Finset.exists_subset_card_eq hz_card with ⟨Z, _hZsub, hZcard⟩
  let u₁ : Fin n → F := fun i => if i ∈ Z then 0 else 1
  have hzero : directionZeroSet u₁ = Z := by
    ext i
    by_cases hi : i ∈ Z <;> simp [directionZeroSet, u₁, hi]
  have hsupport : directionSupportSet u₁ = Zᶜ := by
    ext i
    by_cases hi : i ∈ Z <;> simp [directionSupportSet, u₁, hi]
  refine ⟨u₁, ?_, ?_⟩
  · rw [hzero, hZcard]
  · rw [hsupport, Finset.card_compl, Fintype.card_fin, hZcard]

open Classical in
/-- Parameter-only obstruction for the raw field-power coordinate-fiber fit.  If a possible
large-zero direction can have `z` zero coordinates and still has enough support to activate the
`t` summand, then the field-power fit forces
`choose(z, t) * |F|^(k - t) ≤ B`. -/
theorem not_fieldPowFiberFit_of_zeroCount_choosePow_gt
    (k a B z t : ℕ) (hz : z ≤ n) (hlarge : a ≤ z) (ht : t < a)
    (hsupport : a - t ≤ n - z)
    (hB : B < z.choose t * Fintype.card F ^ (k - t)) :
    ¬ UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B
      (fun t => Fintype.card F ^ (k - t)) := by
  rcases exists_direction_zero_card_eq_support_card_eq (F := F) (n := n) z hz with
    ⟨u₁, hzero, hsupportCard⟩
  exact
    not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_choosePow_gt
      (F := F) (n := n) k a B
      ⟨u₁, by
        rw [SupportEligibleLineDirection, hzero]
        exact not_lt_of_ge hlarge,
        t, ht, by
          rw [hsupportCard]
          exact hsupport,
        by
          rw [hzero]
          exact hB⟩

omit [Fintype F] in
/-- If `2a ≤ n`, there is a large-zero direction whose moving support still has size at least
`a`: choose exactly `a` zero coordinates and put value `1` elsewhere. -/
theorem exists_largeZero_direction_support_ge_of_two_mul_le (a : ℕ) (h2a : 2 * a ≤ n) :
    ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection (F := F) (n := n) a u₁ ∧
      a ≤ (directionSupportSet u₁).card := by
  have ha_le_n : a ≤ n := by omega
  rcases exists_direction_zero_card_eq_support_card_eq (F := F) (n := n) a ha_le_n with
    ⟨u₁, hzero, hsupport⟩
  refine ⟨u₁, ?_, ?_⟩
  · rw [SupportEligibleLineDirection, hzero]
    exact not_lt_of_ge le_rfl
  · rw [hsupport]
    omega

open Classical in
/-- In the common range `2a ≤ n`, the raw field-power coordinate-fiber arithmetic fit is
impossible for any target below `|F|^k`. -/
theorem not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_two_mul_le
    (k a B : ℕ) (ha : 0 < a) (h2a : 2 * a ≤ n) (hB : B < Fintype.card F ^ k) :
    ¬ UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B
      (fun t => Fintype.card F ^ (k - t)) := by
  exact
    not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_support_ge
      (F := F) (n := n) k a B ha hB
      (exists_largeZero_direction_support_ge_of_two_mul_le (F := F) (n := n) a h2a)

section SourceAudit

#print axioms exists_direction_zero_card_eq_support_card_eq
#print axioms not_fieldPowFiberFit_of_zeroCount_choosePow_gt
#print axioms exists_largeZero_direction_support_ge_of_two_mul_le
#print axioms not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_two_mul_le

end SourceAudit

end ProximityGap.Ownership
