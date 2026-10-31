/-
Copyright (c) 2026 Mikhail (mashingaan). All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Mikhail (mashingaan)
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAStepFunction
import Mathlib.Tactic

/-!
# No interior maximum for the repository MCA good-radius set

For every positive finite coordinate count, each radius below one has
an immediately larger radius with the same agreement ceiling. The existing
step-function law therefore gives equal MCA errors at the two radii.

Consequently, the repository good-radius set has a greatest element if and
only if radius one is good. Every greatest element must be one. This settles
the finite-radius attainment question for these definitions, without computing
the supremum or proving whether radius one is good at production parameters.

This addresses the attained-maximum versus supremum obligation in issue #164.
It does not establish sponsor equivalence or close the production prize.
-/

set_option autoImplicit false
open scoped NNReal ENNReal

namespace ProximityGap.Frontier.MCAGoodRadiusMaximum

theorem ceil_radius_right_plateau (n : ℕ) (hn : 0 < n)
    (δ : ℝ≥0) (hδ : δ < 1) :
    ∃ δ' : ℝ≥0, δ < δ' ∧ δ' < 1 ∧
      ⌈(1 - δ) * (n : ℝ≥0)⌉₊ = ⌈(1 - δ') * (n : ℝ≥0)⌉₊ := by
  have hn' : (0 : ℝ≥0) < n := by exact_mod_cast hn
  have hx : (0 : ℝ≥0) < (1 - δ) * (n : ℝ≥0) :=
    mul_pos (tsub_pos_of_lt hδ) hn'
  have ht : ⌈(1 - δ) * (n : ℝ≥0)⌉₊ ≠ 0 :=
    Nat.ne_of_gt (Nat.ceil_pos.mpr hx)
  obtain ⟨hl, hu⟩ := (Nat.ceil_eq_iff ht).mp rfl
  obtain ⟨z, hz₀, hz₁⟩ := exists_between hl
  have hzpos : 0 < z := lt_of_le_of_lt zero_le hz₀
  have hxn : (1 - δ) * (n : ℝ≥0) ≤ n := by
    simpa using mul_le_mul_of_nonneg_right (tsub_le_self : (1 - δ : ℝ≥0) ≤ 1)
      (show (0 : ℝ≥0) ≤ n from zero_le)
  have hzn : z < n := lt_of_lt_of_le hz₁ hxn
  have hdiv : z / (n : ℝ≥0) < 1 := by
    exact (div_lt_one hn').mpr hzn
  let δ' : ℝ≥0 := 1 - z / (n : ℝ≥0)
  have hd' : δ' < 1 := by
    exact tsub_lt_self (by norm_num) (div_pos hzpos hn')
  have hsum : δ' + z / (n : ℝ≥0) = 1 := tsub_add_cancel_of_le (le_of_lt hdiv)
  have hsumδ : δ + (1 - δ) = 1 := add_tsub_cancel_of_le (le_of_lt hδ)
  have hdivsmall : z / (n : ℝ≥0) < 1 - δ := by
    exact (div_lt_iff₀ hn').mpr hz₁
  have hδ' : δ < δ' := by
    nlinarith [hsum, hsumδ]
  have heq : (1 - δ') * (n : ℝ≥0) = z := by
    have hsub : 1 - δ' = z / (n : ℝ≥0) := by
      apply (tsub_eq_iff_eq_add_of_le (le_of_lt hd')).mpr
      simpa [add_comm] using hsum.symm
    rw [hsub, div_mul_cancel₀ _ (ne_of_gt hn')]
  refine ⟨δ', hδ', hd', ?_⟩
  symm
  apply (Nat.ceil_eq_iff ht).mpr
  rw [heq]
  exact ⟨hz₀, le_trans (le_of_lt hz₁) hu⟩

#print axioms ceil_radius_right_plateau
end ProximityGap.Frontier.MCAGoodRadiusMaximum
namespace ProximityGap.Frontier.MCAGoodRadiusMaximum
open ProximityGap ProximityGap.MCAThresholdLedger ProximityGap.MCAStepFunction

variable {ι F A : Type}
variable [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

theorem epsMCA_right_plateau (C : Set (ι → A)) (δ : ℝ≥0) (hδ : δ < 1) :
    ∃ δ' : ℝ≥0, δ < δ' ∧ δ' < 1 ∧
      epsMCA (F := F) (A := A) C δ = epsMCA (F := F) (A := A) C δ' := by
  obtain ⟨δ', hlt, hone, hceil⟩ :=
    ceil_radius_right_plateau (Fintype.card ι) Fintype.card_pos δ hδ
  exact ⟨δ', hlt, hone, epsMCA_eq_of_ceil_eq C hceil⟩

theorem greatest_good_radius_eq_one (C : Set (ι → A)) (ε : ℝ≥0∞) (δ : ℝ≥0)
    (hg : IsGreatest (mcaGoodRadii (F := F) (A := A) C ε) δ) : δ = 1 := by
  by_contra hne
  have hlt : δ < 1 := lt_of_le_of_ne hg.1.1 hne
  obtain ⟨δ', hinc, hbound, heq⟩ := epsMCA_right_plateau (F := F) C δ hlt
  have hgood : δ' ∈ mcaGoodRadii (F := F) (A := A) C ε := by
    refine ⟨le_of_lt hbound, ?_⟩
    rw [← heq]
    exact hg.1.2
  exact (not_lt_of_ge (hg.2 hgood)) hinc

theorem exists_greatest_good_radius_iff (C : Set (ι → A)) (ε : ℝ≥0∞) :
    (∃ δ, IsGreatest (mcaGoodRadii (F := F) (A := A) C ε) δ) ↔
      epsMCA (F := F) (A := A) C 1 ≤ ε := by
  constructor
  · rintro ⟨δ, hg⟩
    have heq := greatest_good_radius_eq_one (F := F) C ε δ hg
    simpa [heq] using hg.1.2
  · intro h
    refine ⟨1, ⟨⟨le_rfl, h⟩, ?_⟩⟩
    intro δ hδ
    exact hδ.1

#print axioms epsMCA_right_plateau
#print axioms greatest_good_radius_eq_one
#print axioms exists_greatest_good_radius_iff
end ProximityGap.Frontier.MCAGoodRadiusMaximum
