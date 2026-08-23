/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement

/-!
# Unique-decoding window for the canonical `PzFamily`

This file proves the `PzFamily` representative uniqueness fact in the ordinary
unique-decoding window.  It is the §5 analogue of the depth-0 K4 uniqueness lemma in
`Hab25CaptureKernelUD`: if two low-degree representatives are both `δ`-close to the same
line word and the two agreement sets must intersect in more points than their degree, the
representatives coincide.

The theorem is intentionally scoped to this window.  The Johnson-range / Hensel-lift regime
remains the separate large-sector capture-kernel problem.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

open Polynomial Finset Function Code
open scoped BigOperators LinearCode NNReal

section RatCloseness

variable {F : Type} [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Convert the BCIKS rational-radius form of relative closeness into the `NNReal` form
used by the generic agreement-set extractor. -/
lemma relHammingDist_le_real_toNNReal_of_rat_le
    {u v : Fin n → F} {δ : ℚ} (hδ0 : 0 ≤ δ)
    (h : δᵣ(u, v) ≤ δ) :
    δᵣ(u, v) ≤ Real.toNNReal (δ : ℝ) := by
  rw [← NNReal.coe_le_coe]
  rw [Real.coe_toNNReal]
  · change (((δᵣ(u, v) : ℚ≥0) : ℚ) : ℝ) ≤ (δ : ℝ)
    exact_mod_cast h
  · exact_mod_cast hδ0

end RatCloseness

section BCIKS20PzFamilyUD

variable {F : Type} [Field F] [DecidableEq F] [Finite F]
variable {n : ℕ} [NeZero n]

/-- **Canonical representative uniqueness in the unique-decoding window.**

Let `P` be any decoded family on the §5 close-parameter set.  If the rational radius is
nonnegative and two `δ`-agreement sets necessarily intersect in at least `k + 1` positions,
then `P` is forced to be the canonical `PzFamily` on that set.

The arithmetic hypothesis is stated in the agreement-set form produced by
`relCloseToWord_iff_exists_agreementCols`:
`n + (k + 1) ≤ 2 * (n - ⌊δ n⌋)`. -/
lemma PzFamily_unique_of_window
    {k : ℕ} {δ : ℚ} {u₀ u₁ : Fin n → F} {ωs : Fin n ↪ F} {P : F → F[X]}
    (hδ0 : 0 ≤ δ)
    (hwin :
      n + (k + 1) ≤
        2 * (n - Nat.floor (Real.toNNReal (δ : ℝ) * (n : ℝ≥0))))
    (hP : ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      (P z).natDegree < k + 1 ∧ δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ δ) :
    ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      P z = PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z := by
  classical
  intro z hz
  have hPz := hP z hz
  have hFamz := PzFamily_decoded_on_close_set
    (F := F) (n := n) (k := k) (δ := δ) (u₀ := u₀) (u₁ := u₁) (ωs := ωs) z hz
  have hPclose :
      δᵣ(u₀ + z • u₁, (P z).eval ∘ ωs) ≤ Real.toNNReal (δ : ℝ) :=
    relHammingDist_le_real_toNNReal_of_rat_le (F := F) (n := n) hδ0 hPz.2
  have hFamclose :
      δᵣ(u₀ + z • u₁,
          (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval ∘ ωs)
        ≤ Real.toNNReal (δ : ℝ) :=
    relHammingDist_le_real_toNNReal_of_rat_le (F := F) (n := n) hδ0 hFamz.2
  obtain ⟨SP, hSP_card, hSP_agree⟩ :=
    (Code.relCloseToWord_iff_exists_agreementCols
      (u := u₀ + z • u₁) (v := (P z).eval ∘ ωs)
      (δ := Real.toNNReal (δ : ℝ))).mp hPclose
  obtain ⟨SF, hSF_card, hSF_agree⟩ :=
    (Code.relCloseToWord_iff_exists_agreementCols
      (u := u₀ + z • u₁)
      (v := (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).eval ∘ ωs)
      (δ := Real.toNNReal (δ : ℝ))).mp hFamclose
  have hSP_card' :
      n - Nat.floor (Real.toNNReal (δ : ℝ) * (n : ℝ≥0)) ≤ SP.card := by
    simpa [Fintype.card_fin] using hSP_card
  have hSF_card' :
      n - Nat.floor (Real.toNNReal (δ : ℝ) * (n : ℝ≥0)) ≤ SF.card := by
    simpa [Fintype.card_fin] using hSF_card
  have hUnion : (SP ∪ SF).card ≤ n := by
    simpa [Fintype.card_fin] using Finset.card_le_univ (SP ∪ SF)
  have hInter : k + 1 ≤ (SP ∩ SF).card := by
    have hUnionInter := Finset.card_union_add_card_inter SP SF
    omega
  have hPdeg : (P z).degree < k + 1 := by
    by_cases hp : P z = 0
    · simp [hp]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mp hPz.1
  have hFamdeg :
      (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).degree < k + 1 := by
    by_cases hp : PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z = 0
    · simp [hp]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mp hFamz.1
  have hdeg :
      (P z - PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).degree < k + 1 :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hPdeg hFamdeg)
  have hzero :
      P z - PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z = 0 := by
    by_cases hdiff : P z - PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z = 0
    · exact hdiff
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (P z - PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z)
      ((SP ∩ SF).image ωs) ?_ ?_
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hiP := (hSP_agree i).1 (Finset.mem_inter.mp hi).1
      have hiF := (hSF_agree i).1 (Finset.mem_inter.mp hi).2
      simp only [Function.comp_apply] at hiP hiF
      rw [Polynomial.eval_sub, ← hiP, ← hiF, sub_self]
    · rw [Finset.card_image_of_injective _ ωs.injective]
      exact lt_of_lt_of_le ((Polynomial.natDegree_lt_iff_degree_lt hdiff).mpr hdeg) hInter
  exact sub_eq_zero.mp hzero

#print axioms relHammingDist_le_real_toNNReal_of_rat_le
#print axioms PzFamily_unique_of_window

end BCIKS20PzFamilyUD

end ProximityGap
