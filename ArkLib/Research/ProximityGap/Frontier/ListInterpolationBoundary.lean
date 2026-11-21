/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.KKH26
import ArkLib.Research.ProximityGap.Frontier.FourRateList128

/-! # The exact list size at dimension-many agreements and the adjacent budget windows

At the radius with exactly `k` required agreements, every positive interleaving width has
worst list size `n.choose k`, independently of the supplied evaluation domain. This is one
Hamming error below the relative minimum distance. At one more
required agreement the packing bound divides this number by `k+1`. At one fewer required
agreement a field line fits inside one ball. Thus two adjacent ranges of integer budgets
give explicit first-failure counts on every injective finite-field domain. -/

namespace ProximityGap.ListInterpolationBoundary

open Code
open scoped ENNReal NNReal

variable {ι F : Type} [Fintype ι] [Nonempty ι] [Field F] [DecidableEq F] [Fintype F]
    (D : ι ↪ F) {k m : ℕ} (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (hm : 0 < m)

/-- Interleaved Reed–Solomon codewords on the supplied domain. -/
abbrev words (D : ι ↪ F) (k m : ℕ) :=
  interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (ι → F))

include hm in
omit [Nonempty ι] [DecidableEq F] [Fintype F] in
private theorem diagonal (δ : ℝ) :
    Lambda (ReedSolomon.code D k : Set (ι → F)) δ ≤ Lambda (words D k m) δ :=
  Lambda_le_of_injective_comp (C := (ReedSolomon.code D k : Set (ι → F)))
    (D := words D k m) (e := fun (a : F) (_ : Fin m) => a)
    (fun _ _ h => congrFun h ⟨0, hm⟩) (fun _ h _ => h) δ

include hk hkn hm in
/-- Worst-center list size at exactly `k` agreements, for any positive interleaving width. -/
theorem at_dimension_agreement :
    Lambda (words D k m) (((Fintype.card ι - k : ℕ) : ℝ) / Fintype.card ι) =
      ((Fintype.card ι).choose k : ℕ∞) := by
  classical
  let n := Fintype.card ι
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply le_antisymm
  · have hu := AgreementSubsetListPacking.interleaved_lambda_le_choose_div D k k m
      (((Fintype.card ι - k : ℕ) : ℝ) / Fintype.card ι) le_rfl
      (by rw [div_mul_cancel₀ _ hn.ne', Nat.cast_sub hkn]; linarith)
    simpa only [Nat.choose_self, Nat.div_one] using hu
  · let H := Finset.univ.image D
    have hcard : H.card = n := by
      dsimp [H, n]
      rw [Finset.card_image_of_injective _ D.injective, Finset.card_univ]
    have hfib (y : F) (hy : y ∈ H) :
        (Finset.univ.filter fun i => D i ^ 1 = y).card = 1 := by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      apply Finset.card_eq_one.mpr
      refine ⟨i, ?_⟩
      ext j
      simp [D.injective.eq_iff]
    have hl := CodingTheory.AdditiveSetListDecoding.choose_le_Lambda_rs_vanilla D
      (d := 1) (h := n) (khat := k) (k := k) (by simp [n]) hcard hfib
      (by omega) (by simp)
    rw [CodingTheory.AdditiveSetListDecoding.minRelDist_sub_eq D
      (d := 1) (h := n) (khat := k) (k := k) (by simp [n]) hk hkn (by simp)] at hl
    have heq : 1 - (k : ℝ) / n = ((Fintype.card ι - k : ℕ) : ℝ) / Fintype.card ι := by
      dsimp [n]
      rw [Nat.cast_sub hkn, sub_div, div_self hn.ne']
    rw [heq] at hl
    exact hl.trans (diagonal D hm _)

include hk hkn hm in
/-- In the budget range from the packing bound up to field size, the first failure
is at `n-k` or `n-k+1` as determined by the binomial coefficient. -/
theorem good_iff {B : ℕ} (hpack : (Fintype.card ι).choose k / (k + 1) ≤ B)
    (hfield : B < Fintype.card F) (δ : ℝ) :
    Lambda (words D k m) δ ≤ (B : ℕ∞) ↔
      δ < (((if (Fintype.card ι).choose k ≤ B then Fintype.card ι - k + 1
        else Fintype.card ι - k) : ℕ) : ℝ) / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  by_cases hB : (Fintype.card ι).choose k ≤ B
  · rw [ite_eq_left hB]
    constructor
    · contrapose!
      intro hδ
      have : NeZero k := ⟨hk.ne'⟩
      have hd := ReedSolomon.minDist_of_le (α := D) (n := k) hkn
      have hc := FieldListAtMinimumDistance.field_card_le_lambda (ReedSolomon.code D k)
        (hd ▸ (show 0 < Fintype.card ι - k + 1 by omega))
      rw [hd] at hc
      exact (show (B : ℕ∞) < Fintype.card F by exact_mod_cast hfield).trans_le
        (hc.trans ((diagonal D hm _).trans (Lambda_mono hδ)))
    · intro hδ
      have hu := AgreementSubsetListPacking.interleaved_lambda_le_choose_div D k k m δ le_rfl
        (by rw [lt_div_iff₀ hn, Nat.cast_add, Nat.cast_sub hkn, Nat.cast_one] at hδ; linarith)
      simp only [Nat.choose_self, Nat.div_one] at hu
      exact hu.trans (by exact_mod_cast hB)
  · rw [ite_eq_right hB]
    constructor
    · contrapose!
      intro hδ
      have hbig : (B : ℕ∞) < ((Fintype.card ι).choose k : ℕ) := by
        exact_mod_cast Nat.lt_of_not_ge hB
      rw [← at_dimension_agreement D hk hkn hm] at hbig
      exact hbig.trans_le (Lambda_mono hδ)
    · intro hδ
      have hu := AgreementSubsetListPacking.interleaved_lambda_le_choose_div D k (k+1) m δ
        (Nat.le_succ k) (by rw [lt_div_iff₀ hn, Nat.cast_sub hkn] at hδ; push_cast; linarith)
      rw [Nat.choose_succ_self_right] at hu
      exact hu.trans (by exact_mod_cast hpack)

include hk hkn hm in
/-- The two adjacent first-failure counts for the sponsor's 128-bit list predicate,
at every radius, on the supplied domain. -/
theorem prize_good_iff
    (hpack : (Fintype.card ι).choose k / (k + 1) ≤ Fintype.card F / 2 ^ 128) (δ : ℝ) :
    (Lambda (words D k m) δ : ENNReal) ≤
        ((prizeThreshold : ℝ≥0) : ENNReal) * Fintype.card F ↔
      δ < (((if (Fintype.card ι).choose k ≤ Fintype.card F / 2 ^ 128
        then Fintype.card ι - k + 1 else Fintype.card ι - k) : ℕ) : ℝ) / Fintype.card ι := by
  rw [FourRateList128.budget_cast]
  exact good_iff D hk hkn hm hpack (Nat.div_lt_self Fintype.card_pos (by decide)) δ

include hk hkn hm in
/-- If the field has at least `2^(128+n)` elements, the first list failure at 128-bit
security is exactly the minimum distance, simultaneously for every dimension and domain. -/
theorem large_field {δ : ℝ} (hq : 2 ^ (128 + Fintype.card ι) ≤ Fintype.card F) :
    (Lambda (words D k m) δ : ENNReal) ≤
        ((prizeThreshold : ℝ≥0) : ENNReal) * Fintype.card F ↔
      δ < ((Fintype.card ι - k + 1 : ℕ) : ℝ) / Fintype.card ι := by
  have hB : (Fintype.card ι).choose k ≤ Fintype.card F / 2 ^ 128 := by
    apply (Nat.choose_le_two_pow _ _).trans
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2 ^ 128)).mpr
    simpa only [pow_add, Nat.mul_comm] using hq
  simpa only [ite_eq_left hB] using
    prize_good_iff D hk hkn hm ((Nat.div_le_self _ _).trans hB) δ

#print axioms at_dimension_agreement
#print axioms good_iff
#print axioms prize_good_iff
#print axioms large_field

end ProximityGap.ListInterpolationBoundary
