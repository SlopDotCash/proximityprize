/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Research.ProximityGap.Frontier.AgreementSubsetListPacking
import ArkLib.Research.ProximityGap.Frontier.BlsScalarSubgroup
import ArkLib.Research.ProximityGap.Frontier.FieldListAtMinimumDistance
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection
import ArkLib.Research.ProximityGap.Frontier.PrescribedProductList

/-!
# Exact list thresholds on the BLS12-381 scalar subgroup of order 256

At dimension 32, 34 agreements suffice for safety by incidence counting, while a prescribed
product of 33 subgroup elements yields a scalar list exceeding the 128-bit prize budget.
At dimension 16, packing suffices at 16 agreements and a minimum-weight line overflows at 15.
-/

namespace ProximityGap.BlsScalarListThreshold

open Code BlsScalarSubgroup GrandChallenges
open scoped NNReal ENNReal

/-- The length-256 subgroup of the BLS12-381 scalar field. -/
abbrev H := Subgroup.zpowers generator

noncomputable instance fintypeH : Fintype H := Fintype.ofFinite H

theorem card_H : Fintype.card H = 256 := by
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_zpowers _).trans generator_order

/-- Evaluation at each element of the subgroup. -/
def domain : H ↪ ZMod P :=
  ⟨fun x ↦ ((x : (ZMod P)ˣ) : ZMod P), fun _ _ h ↦ Subtype.ext (Units.ext h)⟩

noncomputable instance smoothDomain : ReedSolomon.Smooth domain where
  H := H
  a := 1
  h_card_pow2 := ⟨8, card_H⟩
  h_coset := by
    classical
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i.val, i.property, one_mul _⟩
    · rintro ⟨i, hi, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, (one_mul _).symm⟩

/-- Integer list budget at the BLS12-381 scalar modulus. -/
abbrev B : ℕ := P / 2^128

private theorem budget_cast (l : ℕ∞) :
    (l : ENNReal) ≤ ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card (ZMod P) : ENNReal) ↔
      l ≤ B := by
  have hε : (prizeThreshold : ℝ≥0) = 1 / 2^128 := by norm_num [prizeThreshold]
  have hlo : (B : ℝ≥0) ≤ (1 / 2^128 : ℝ≥0) * P := by
    norm_num [B, P]
    rw [le_div_iff₀ (by positivity)]
    norm_num
  have hhi : (1 / 2^128 : ℝ≥0) * P < ((B + 1 : ℕ) : ℝ≥0) := by norm_num [B, P]
  have hl : (B : ENNReal) ≤ ((1 / 2^128 : ℝ≥0) : ENNReal) * P := by exact_mod_cast hlo
  have hu : ((1 / 2^128 : ℝ≥0) : ENNReal) * P < ((B + 1 : ℕ) : ENNReal) := by exact_mod_cast hhi
  rw [hε, ZMod.card]
  constructor
  · intro h
    have hlt : l < ((B+1 : ℕ) : ℕ∞) := by exact_mod_cast (h.trans_lt hu)
    induction l using ENat.recTopCoe with
    | top => simp at hlt
    | coe n =>
      exact_mod_cast (Nat.le_of_lt_succ (show n < B + 1 by exact_mod_cast hlt))
  · intro h
    exact (show (l : ENNReal) ≤ B by exact_mod_cast h).trans hl

private theorem scalar_le_of_le {m k : ℕ} (hm : 0 < m) (δ : ℝ)
    (h : Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code domain k : Set (H → ZMod P)))
      δ ≤ B) : Lambda (ReedSolomon.code domain k : Set (H → ZMod P)) δ ≤ B := by
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have ht := InterleavedListProjection.prize_list_budget_iff
    (κ := Fin m) (ReedSolomon.code domain k) δ (by
      rw [Nat.card_eq_fintype_card, ZMod.card]; decide)
  rw [Nat.card_eq_fintype_card, ZMod.card] at ht
  exact ht.mp h

/-- All positive widths at dimension 32 have their first unsafe Hamming radius at 223 errors. -/
theorem rateEighth (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code domain 32 : Set (H → ZMod P))) δ :
      ENNReal) ≤ ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card (ZMod P) : ENNReal) ↔
        δ < (223 : ℝ) / 256 := by
  rw [budget_cast]
  constructor
  · intro h
    by_contra! hδ
    have hscalar := scalar_le_of_le hm δ h
    have hlower := PrescribedProductList.exceeds_budget domain H id (fun _ ↦ rfl)
      (k := 32) (B := B) (by decide) (by
        rw [card_H, Nat.choose_eq_descFactorial_div_factorial]; decide)
    rw [card_H] at hlower
    norm_num only [Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat] at hlower
    exact (not_lt_of_ge hscalar) (hlower.trans_le (Lambda_mono hδ))
  · intro hδ
    have hu := AgreementSubsetListPacking.interleaved_lambda_le_choose_div domain 32 34 m δ
      (by decide) (by rw [card_H]; norm_num; linarith)
    rw [card_H] at hu
    apply hu.trans
    exact_mod_cast (show Nat.choose 256 32 / Nat.choose 34 32 ≤ B by
      simp only [Nat.choose_eq_descFactorial_div_factorial]; decide)

/-- The exact rate-one-eighth boundary in the canonical resolution type. -/
noncomputable def rateEighthResolution (m : ℕ) (hm : 0 < m) :
    GrandListResolution (ReedSolomon.code domain 32 : Set (H → ZMod P)) m
      (prizeThreshold : ℝ≥0) := by
  refine ⟨222, by rw [card_H]; decide, ?_, ?_⟩
  · apply (rateEighth m hm _).mpr
    norm_num [gridPt, card_H]
  · apply lt_of_not_ge
    intro h
    have hn := (rateEighth m hm (gridPt (ι := H) (222+1) : ℝ)).mp h
    norm_num [gridPt, card_H] at hn

/-- The official smooth-domain challenge at prize index two. -/
theorem grandListDecodingChallengeRs_rateEighth (m : ℕ) (hm : 0 < m) :
    grandListDecodingChallengeRs domain (prizeDimension (ι := H) 2) m
      (prizeThreshold : ℝ≥0) := by
  have hk : prizeDimension (ι := H) 2 = 32 := by
    norm_num [prizeDimension, prizeDenominator, card_H]
  rw [hk]
  exact (rateEighthResolution m hm).to_challenge

/-- At dimension 16, the budget already covers every list with 16 agreements.
At 15 agreements the entire field indexes a list in the ball about zero. -/
theorem rateSixteenth (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code domain 16 : Set (H → ZMod P))) δ :
      ENNReal) ≤ ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card (ZMod P) : ENNReal) ↔
        δ < (241 : ℝ) / 256 := by
  rw [budget_cast]
  constructor
  · intro h
    by_contra! hδ
    have hscalar := scalar_le_of_le hm δ h
    have hd : Code.minDist (ReedSolomon.code domain 16 : Set (H → ZMod P)) = 241 := by
      rw [ReedSolomon.minDist_of_le (by rw [card_H]; decide : 16 ≤ Fintype.card H), card_H]
    have hlower := FieldListAtMinimumDistance.field_card_le_lambda
      (ReedSolomon.code domain 16) (by rw [hd]; decide)
    rw [hd, card_H, ZMod.card] at hlower
    have hbudget : (B : ℕ∞) < P := by exact_mod_cast (show B < P by decide)
    exact (not_lt_of_ge hscalar) (hbudget.trans_le (hlower.trans (Lambda_mono hδ)))
  · intro hδ
    have hu := AgreementSubsetListPacking.interleaved_lambda_le_choose_div domain 16 16 m δ
      (by decide) (by rw [card_H]; norm_num; linarith)
    rw [card_H, Nat.choose_self, Nat.div_one] at hu
    apply hu.trans
    exact_mod_cast (show Nat.choose 256 16 ≤ B by
      rw [Nat.choose_eq_descFactorial_div_factorial]; decide)

/-- The exact rate-one-sixteenth boundary in the canonical resolution type. -/
noncomputable def rateSixteenthResolution (m : ℕ) (hm : 0 < m) :
    GrandListResolution (ReedSolomon.code domain 16 : Set (H → ZMod P)) m
      (prizeThreshold : ℝ≥0) := by
  refine ⟨240, by rw [card_H]; decide, ?_, ?_⟩
  · apply (rateSixteenth m hm _).mpr
    norm_num [gridPt, card_H]
  · apply lt_of_not_ge
    intro h
    have hn := (rateSixteenth m hm (gridPt (ι := H) (240+1) : ℝ)).mp h
    norm_num [gridPt, card_H] at hn

/-- The official smooth-domain challenge at prize index three. -/
theorem grandListDecodingChallengeRs_rateSixteenth (m : ℕ) (hm : 0 < m) :
    grandListDecodingChallengeRs domain (prizeDimension (ι := H) 3) m
      (prizeThreshold : ℝ≥0) := by
  have hk : prizeDimension (ι := H) 3 = 16 := by
    norm_num [prizeDimension, prizeDenominator, card_H]
  rw [hk]
  exact (rateSixteenthResolution m hm).to_challenge

#print axioms rateSixteenth
#print axioms grandListDecodingChallengeRs_rateSixteenth
#print axioms rateEighth
#print axioms grandListDecodingChallengeRs_rateEighth

end ProximityGap.BlsScalarListThreshold
