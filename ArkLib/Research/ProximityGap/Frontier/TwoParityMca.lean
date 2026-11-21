/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.MCAEndpointLower
import ArkLib.Research.ProximityGap.MCAZeroUpperBound
import ArkLib.Data.CodingTheory.ProximityGap.MCAStepFunction
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA
import ArkLib.Research.ProximityGap.MCAPlateauWindow
import ArkLib.Research.ProximityGap.Frontier.CircuitDensity
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-! # The line-MCA profile with two parity checks

When the dimension is two less than the length, the largest useful witness
supports omit one site. Their sums differ by the omitted domain value, so
the subset-sum lower bound attains the circuit upper bound over every field.
-/

open Finset
open scoped NNReal ENNReal
namespace ProximityGap.TwoParityMca

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F]

omit [Nonempty I] [Fintype F] in
/-- Omitting each coordinate gives a different sum on a support of size k+1. -/
theorem omitted_sums (D : I ↪ F) {k : ℕ} (hn : Fintype.card I = k+2) :
    Fintype.card I ≤ (subsetSumsKplus1 D k).card := by
  classical
  let a (i : I) := ∑ j ∈ (univ.erase i), D j
  have relation (i : I) : a i + D i = ∑ j, D j := sum_erase_add _ _ (mem_univ i)
  have hinj : Function.Injective a := by
    intro i j eq
    apply D.injective
    exact add_left_cancel (eq ▸ (relation i).trans (relation j).symm)
  have hsub : univ.image a ⊆ subsetSumsKplus1 D k := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    apply mem_image.mpr
    exact ⟨univ.erase i, mem_powersetCard.mpr ⟨subset_univ _, by simp [hn]⟩, rfl⟩
  simpa only [card_image_of_injective _ hinj, card_univ] using card_le_card hsub

/-- From one error through the saturated radius, the worst numerator equals n
for every injective domain and every finite field, including fields of order n. -/
theorem exact (D : I ↪ F) {k : ℕ} (hn : Fintype.card I = k+2) (δ : ℝ≥0)
    (hδ : (1-δ)*(Fintype.card I : ℝ≥0) ≤ (k : ℝ≥0)+1) :
    epsMCA (F:=F) (ReedSolomon.code D k : Set (I → F)) δ =
      (Fintype.card I : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) := by
  classical
  apply le_antisymm
  · apply epsMCA_le_of_badCount_le
    intro u
    have h := CircuitDensity.mca_count_le_choose D k δ (u 0) (u 1)
    have eq : (Fintype.card I).choose (k+1) = Fintype.card I := by
      rw [Nat.choose_symm_of_eq_add (show Fintype.card I = (k+1)+1 by omega), Nat.choose_one_right]
    exact h.trans_eq eq
  · rw [epsMCA_eq_epsMCA_one_of_le_succ D k hδ]
    apply le_trans _ (epsMCA_one_ge_card_subsetSums D (by omega : k+1 ≤ Fintype.card I))
    exact ENNReal.div_le_div_right (by exact_mod_cast omitted_sums D hn) _

/-- Complete probability curve on real radii. The closed ball jumps at one
error from one bad scalar to as many bad scalars as evaluation points. -/
theorem profile (D : I ↪ F) {k : ℕ} (hn : Fintype.card I = k+2) (δ : ℝ≥0) :
    epsMCA (F:=F) (ReedSolomon.code D k : Set (I → F)) δ =
      (if 1/(Fintype.card I : ℝ≥0) ≤ δ then (Fintype.card I : ℝ≥0∞) else 1) /
        (Fintype.card F : ℝ≥0∞) := by
  have hn₀ : (0 : ℝ≥0) < Fintype.card I := by exact_mod_cast Fintype.card_pos (α:=I)
  have hcast : (Fintype.card I : ℝ≥0) = (k : ℝ≥0)+2 := by exact_mod_cast hn
  have cell : (1-δ)*(Fintype.card I : ℝ≥0) ≤ (k : ℝ≥0)+1 ↔ 1/(Fintype.card I : ℝ≥0) ≤ δ := by
    rw [tsub_mul, one_mul, tsub_le_iff_right, div_le_iff₀ hn₀]
    constructor <;> intro h <;> linarith
  split_ifs with h
  · exact exact D hn δ (cell.mpr h)
  · have low := lt_of_not_ge (fun hh => h (cell.mp hh))
    have ceil : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = Fintype.card I := by
      apply (Nat.ceil_eq_iff Fintype.card_ne_zero).mpr
      refine ⟨?_, ?_⟩
      · simpa only [show Fintype.card I-1=k+1 by omega, Nat.cast_add, Nat.cast_one] using low
      · exact (mul_le_mul_of_nonneg_right (tsub_le_self : 1-δ ≤ 1) (by positivity)).trans_eq (one_mul _)
    rw [MCAStepFunction.epsMCA_eq_of_ceil_eq (δ':=0) _ (by simpa using ceil)]
    apply le_antisymm (epsMCA_zero_le_inv _)
    simpa only [one_div] using (epsMCA_ge_inv_card D k 0 (by omega))

/-- The same two values apply at every positive interleaving width. -/
theorem interleaved_profile (D : I ↪ F) {k : ℕ} (hn : Fintype.card I = k+2)
    (width : ℕ) [NeZero width] (δ : ℝ≥0) :
    epsMCA (F:=F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin width)) δ =
      (if 1/(Fintype.card I : ℝ≥0) ≤ δ then (Fintype.card I : ℝ≥0∞) else 1) /
        (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA_interleaved_eq, profile D hn]

#print axioms interleaved_profile
#print axioms exact
#print axioms profile
end ProximityGap.TwoParityMca
