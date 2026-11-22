/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Research.ProximityGap.Frontier.AgreementSubsetListPacking
import ArkLib.Research.ProximityGap.Frontier.FieldListAtMinimumDistance
import ArkLib.Data.CodingTheory.ListDecodability.SymbolMap
import ArkLib.Research.ProximityGap.Frontier.PrescribedProductList

/-! # An interval of field sizes with four exact length-128 list thresholds

For any 128-element multiplicative subgroup, the budget interval below has the same
four first bad error counts. This includes both prime fields and extension fields.
-/

namespace ProximityGap.FourRateList128

open Code GrandChallenges
open scoped NNReal ENNReal

variable {K : Type} [Field K] [DecidableEq K] [Fintype K] (H : Subgroup Kˣ) [Fintype H]

/-- The budget interval where 66 agreements suffice for packing at dimension 64
and some prescribed-product class of 65-subsets exceeds budget. -/
structure BudgetWindow (q : ℕ) : Prop where
  packing : (Nat.choose 128 64 / Nat.choose 66 64) ≤ q / 2^128
  product : 128 * (q / 2^128) < Nat.choose 128 65

/-- Inclusion of a multiplicative subgroup as an evaluation domain. -/
def domain : H ↪ K :=
  ⟨fun i ↦ ((i : Kˣ) : K), fun _ _ h ↦ Subtype.ext (Units.ext h)⟩

/-- The inclusion of every dyadic-order multiplicative subgroup is a smooth domain. -/
@[instance_reducible] noncomputable def smooth_of_two_pow {e : ℕ} (card_H : Fintype.card H = 2^e) :
    ReedSolomon.Smooth (domain H) where
  H := H
  a := 1
  h_card_pow2 := ⟨e, card_H⟩
  h_coset := by
    classical
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i.val, i.property, one_mul _⟩
    · rintro ⟨i, hi, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, (one_mul _).symm⟩

/-- Any multiplicative subgroup of order 128 defines a smooth domain. -/
@[instance_reducible] noncomputable def smooth (card_H : Fintype.card H = 128) : ReedSolomon.Smooth (domain H) :=
  smooth_of_two_pow H (e := 7) card_H

/-- First over-budget error count, ordered by decreasing prize rate. -/
def firstBad : Fin 4 → ℕ := ![63, 97, 113, 121]

/-- The grand challenge compares integer list sizes to exactly this natural budget. -/
theorem budget_cast (q : ℕ) (L : ℕ∞) :
    (L : ENNReal) ≤ ((prizeThreshold : ℝ≥0) : ENNReal) * (q : ENNReal) ↔
      L ≤ (q / 2^128 : ℕ) := by
  have hε : (prizeThreshold : ℝ≥0) = 1 / 2^128 := by norm_num [prizeThreshold]
  rw [hε, ← ENNReal.coe_natCast, ← ENNReal.coe_mul]
  induction L using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top, top_le_iff, ENNReal.coe_ne_top, ENat.natCast_ne_top]
  | coe v =>
    have hreal : (v : ℝ≥0) ≤ (1 / 2^128 : ℝ≥0) * q ↔ v ≤ q / 2^128 := by
      rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
      exact_mod_cast (Nat.le_div_iff_mul_le (by decide : 0 < 2^128)).symm
    simpa only [ENat.toENNReal_coe, ← ENNReal.coe_natCast, ENNReal.coe_le_coe,
      ENat.natCast_le_natCast] using hreal

variable (card_H : Fintype.card H = 128) (window : BudgetWindow (Fintype.card K))
private abbrev budget (F : Type) [Fintype F] := Fintype.card F / 2^128

include card_H

private theorem scalar_small_bad (k : ℕ) [NeZero k] (hk : k ≤ 128) :
    (budget K : ℕ∞) < Lambda (ReedSolomon.code (domain H) k : Set (H → K))
      (((128-k+1 : ℕ) : ℝ)/128) := by
  have hdist := ReedSolomon.minDist_of_le (α := domain H) (n := k) (card_H ▸ hk)
  rw [card_H] at hdist
  have h := FieldListAtMinimumDistance.field_card_le_lambda (ReedSolomon.code (domain H) k)
    (hdist ▸ (show 0 < 128-k+1 by omega))
  rw [hdist, card_H] at h
  have hsmall : budget K < Fintype.card K := Nat.div_lt_self Fintype.card_pos (by decide)
  exact (show (budget K : ℕ∞) < Fintype.card K by exact_mod_cast hsmall).trans_le h

include window

private theorem scalar_bad (j : Fin 4) :
    (budget K : ℕ∞) < Lambda (ReedSolomon.code (domain H) (prizeDimension (ι := H) j) : Set (H → K))
      ((firstBad j : ℝ) / 128) := by
  fin_cases j
  · have h := PrescribedProductList.exceeds_budget (domain H) H id (fun _ ↦ rfl)
      (k := 64) (B := budget K) (by decide) (by rw [card_H]; exact window.product)
    rw [card_H] at h
    simpa [prizeDimension, prizeDenominator, card_H, firstBad] using h
  · simpa [prizeDimension, prizeDenominator, card_H, firstBad] using
      scalar_small_bad H card_H 32 (by decide)
  · simpa [prizeDimension, prizeDenominator, card_H, firstBad] using
      scalar_small_bad H card_H 16 (by decide)
  · simpa [prizeDimension, prizeDenominator, card_H, firstBad] using
      scalar_small_bad H card_H 8 (by decide)

/-- The exact real-radius test for all four rates and every positive width. -/
theorem list_threshold (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code (domain H) (prizeDimension (ι := H) j) : Set (H → K))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card K : ENNReal) ↔
        δ < (firstBad j : ℝ)/128 := by
  rw [budget_cast]
  constructor
  · intro h
    by_contra! hδ
    let e : K → Fin m → K := fun a _ ↦ a
    have inj : Function.Injective e := fun _ _ heq ↦ congrFun heq ⟨0, hm⟩
    have hdiag := Code.Lambda_le_of_injective_comp (e := e) inj
      (C := (ReedSolomon.code (domain H) (prizeDimension (ι := H) j) : Set (H → K)))
      (D := interleavedCodeSet (κ := Fin m)
        (ReedSolomon.code (domain H) (prizeDimension (ι := H) j) : Set (H → K)))
      (fun _ hc _ ↦ hc) δ
    exact (not_lt_of_ge (hdiag.trans h)) ((scalar_bad H card_H window j).trans_le (Lambda_mono hδ))
  · intro hδ
    let k := prizeDimension (ι := H) j
    let t := 129 - firstBad j
    have hkt : k ≤ t := by
      fin_cases j <;> norm_num [k, t, prizeDimension, prizeDenominator, card_H, firstBad]
    have ht : (t : ℝ) + firstBad j = 129 := by
      fin_cases j <;> norm_num [t, firstBad]
    have hu := AgreementSubsetListPacking.interleaved_lambda_le_choose_div (domain H) k t m δ hkt
      (by rw [card_H]; norm_num; linarith)
    rw [card_H] at hu
    apply hu.trans
    have hbound : Nat.choose 128 k / Nat.choose t k ≤ Nat.choose 128 64 / Nat.choose 66 64 := by
      fin_cases j <;>
        simp only [k, t, prizeDimension, prizeDenominator, card_H, firstBad,
          Nat.choose_eq_descFactorial_div_factorial] <;> decide
    exact_mod_cast hbound.trans window.packing

/-- Explicit adjacent grid witnesses for a subgroup satisfying the window. -/
noncomputable def resolution (j : Fin 4) (m : ℕ) (hm : 0 < m) :
    GrandListResolution (ReedSolomon.code (domain H) (prizeDimension (ι := H) j) : Set (H → K))
      m (prizeThreshold : ℝ≥0) := by
  refine ⟨firstBad j - 1, ?_, ?_, ?_⟩
  · rw [card_H]
    fin_cases j <;> decide
  · apply (list_threshold H card_H window j m hm _).mpr
    fin_cases j <;> norm_num [gridPt, card_H, firstBad]
  · apply lt_of_not_ge
    intro h
    have hδ := (list_threshold H card_H window j m hm _).mp h
    fin_cases j <;> norm_num [gridPt, card_H, firstBad] at hδ

/-- The complete four-rate grand list prize for every subgroup in the stated interval. -/
theorem listDecodingPrize_all_rates [ReedSolomon.Smooth (domain H)] (m : ℕ) (hm : 0 < m) :
    listDecodingPrize (domain H) m :=
  ⟨hm, PrizeDomainAdmissible.of_smooth (domain H) (by rw [card_H]; decide),
    fun j ↦ (resolution H card_H window j m hm).to_challenge⟩

end ProximityGap.FourRateList128

#print axioms ProximityGap.FourRateList128.listDecodingPrize_all_rates
