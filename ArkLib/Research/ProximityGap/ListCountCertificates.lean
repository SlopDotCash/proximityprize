/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.BoundedChoose
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank
import ArkLib.Research.ProximityGap.Frontier.ListInterpolationBoundary
import ArkLib.Research.ProximityGap.Frontier.RateHalfRichHeadCensus

/-! # Parameter-only decisions at an individual list search step -/

namespace ProximityPrize.ListCountCertificates

open Code ProximityGap
open scoped ENNReal

/-- Decide a closed list test by interpolation, field size, or the integer
second-moment inequality. A missing value sends this count to the support-rank test. -/
def test (n k q m B t : ℕ) : Option Bool :=
  if 0 < m ∧ 0 < k ∧ t = k then
    some (decide (BoundedChoose.capped n k (B + 1) ≤ B))
  else if 0 < m ∧ t < k ∧ B < q then some false
  else
    let L := B + 1
    let x := L * t / n
    if n * x * (x + 1) + (k - 1) * L * (L - 1) < 2 * x * L * t then some true
    else none

private theorem safe_of_incidence {F I : Type} [Fintype I] [Nonempty I] [Field F]
    (D : I ↪ F) (k m B t x : ℕ)
    (strict : Fintype.card I * x * (x + 1) + (k - 1) * (B + 1) * B <
      2 * x * (B + 1) * t) :
    Lambda (ListInterpolationBoundary.words D k m) (1 - (t : ℝ) / Fintype.card I) ≤ (B : ℕ∞) := by
  classical
  apply InterleavedListJohnsonRank.interleaved_lambda_le_of_block_bound D k t m B
  · rw [sub_mul, one_mul, div_mul_cancel₀ _ (by exact_mod_cast Fintype.card_ne_zero)]
    linarith
  · intro s S hw hp
    by_contra! hs
    let e : Fin (B + 1) → Fin s := Fin.castLE hs
    have hi : Function.Injective e := Fin.castLE_injective _
    have bound := RateHalfRichHeadCensus.incidence_bound (fun i => S (e i))
      (fun i => (hw (e i)).ge) (fun _ _ h => hp (hi.ne h)) x
    simp only [Nat.add_sub_cancel] at bound
    nlinarith only [strict, bound]

/-- Every Boolean supplied by the fast test is the exact list-safety verdict. -/
theorem test_correct {F I : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F]
    (D : I ↪ F) {k m B t : ℕ} (hk : k ≤ Fintype.card I) {b : Bool}
    (result : test (Fintype.card I) k (Fintype.card F) m B t = some b) :
    b = true ↔
      Lambda (ListInterpolationBoundary.words D k m) (1 - (t : ℝ) / Fintype.card I) ≤ (B : ℕ∞) := by
  classical
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  unfold test at result
  split at result
  · obtain ⟨hm, hkp, rfl⟩ := ‹0 < m ∧ 0 < k ∧ t = k›
    cases result
    have radius : 1 - (t : ℝ) / Fintype.card I =
        ((Fintype.card I - t : ℕ) : ℝ) / Fintype.card I := by
      rw [Nat.cast_sub hk, sub_div, div_self hn.ne']
    rw [radius, ListInterpolationBoundary.at_dimension_agreement D hkp hk hm,
      decide_eq_true_eq, BoundedChoose.capped_eq]
    simp
  · split at result
    · obtain ⟨hm, htk, hB⟩ := ‹0 < m ∧ t < k ∧ B < Fintype.card F›
      cases result
      simp only [Bool.false_eq_true, false_iff, not_le]
      apply (show (B : ℕ∞) < Fintype.card F by exact_mod_cast hB).trans_le
      have : NeZero k := ⟨by omega⟩
      have hd := ReedSolomon.minDist_of_le (α := D) (n := k) hk
      have field := FieldListAtMinimumDistance.field_card_le_lambda (ReedSolomon.code D k)
        (hd ▸ (show 0 < Fintype.card I - k + 1 by omega))
      rw [hd] at field
      apply field.trans
      apply le_trans (Lambda_le_of_injective_comp (C := (ReedSolomon.code D k : Set (I → F)))
        (D := ListInterpolationBoundary.words D k m) (e := fun (x : F) (_ : Fin m) => x)
        (fun _ _ h => congrFun h ⟨0, hm⟩) (fun _ h _ => h) _)
      apply Lambda_mono
      rw [div_le_iff₀ hn, sub_mul, one_mul, div_mul_cancel₀ _ hn.ne', Nat.cast_add,
        Nat.cast_sub hk, Nat.cast_one]
      have step : (t : ℝ) + 1 ≤ k := by exact_mod_cast htk
      linarith
    · dsimp only at result
      split at result
      · cases result
        exact iff_of_true rfl (safe_of_incidence D k m B t _ (by simpa using ‹_ < _›))
      · cases result

end ProximityPrize.ListCountCertificates
