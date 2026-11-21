/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Research.ProximityGap.Frontier.AgreementSubsetListPacking
import ArkLib.Research.ProximityGap.Frontier.FieldListAtMinimumDistance
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection
import ArkLib.Research.ProximityGap.Frontier.PrescribedProductList
import ArkLib.Research.ProximityGap.Frontier.ReservedFiberList
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.NormNum.Prime

/-!
# Four exact list-decoding thresholds on the 32nd roots of unity in GF(673^16)

At security error `2^-128`, the first over-budget radii for dimensions
`16, 8, 4, 2` are `15/32, 24/32, 29/32, 31/32`. The same thresholds
hold for every positive interleaving width. At half rate the product fibers
of 17-subsets give a list at 17 agreements. The quarter-rate crossing occurs at
capacity. The two lower rates first exceed the budget one Hamming step past capacity.
-/

namespace ProximityGap.FourRateList673

open Code GrandChallenges
open scoped NNReal ENNReal

instance : Fact (Nat.Prime 673) := ⟨by norm_num⟩

/-- The 151-bit alphabet. -/
abbrev K := GaloisField 673 16

noncomputable instance : Fintype K := Fintype.ofFinite K
noncomputable instance : DecidableEq K := Classical.decEq K

/-- The subgroup of 32nd roots of unity used as the coordinate type. -/
noncomputable def U : Subgroup Kˣ := rootsOfUnity 32 K

noncomputable instance : Fintype U := Fintype.ofFinite U

theorem card_K : Fintype.card K = 673^16 :=
  Nat.card_eq_fintype_card.symm.trans (GaloisField.card 673 16 (by decide))

theorem card_U : Fintype.card U = 32 := by
  have h : IsPrimitiveRoot (107 : ZMod 673) 32 := IsPrimitiveRoot.iff_orderOf.mpr
    (orderOf_eq_prime_pow (p := 2) (n := 4) (by decide) (by decide))
  rw [← Nat.card_eq_fintype_card]
  exact (h.map_of_injective (algebraMap (ZMod 673) K).injective).card_rootsOfUnity

/-- Express each subgroup point as a singleton fiber for the reserved-fiber construction. -/
abbrev H := U × Fin 1

theorem card_H : Fintype.card H = 32 := by simp [H, Fintype.card_prod, card_U]

attribute [local simp] card_U

/-- Inclusion of the order-32 subgroup in the extension field. -/
def inclusion : U ↪ K :=
  ⟨fun i ↦ ((i : Kˣ) : K), fun _ _ h ↦ Subtype.ext (Units.ext h)⟩

/-- Evaluation at the unique coordinate of each singleton fiber. -/
def domain : H ↪ K :=
  ⟨fun z ↦ inclusion z.1, fun _ _ h ↦ Prod.ext (inclusion.injective h) (Subsingleton.elim _ _)⟩

noncomputable instance : ReedSolomon.Smooth domain where
  H := U
  a := 1
  h_card_pow2 := ⟨5, card_H⟩
  h_coset := by
    classical
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i.1.val, i.1.property, one_mul _⟩
    · rintro ⟨i, hi, rfl⟩
      exact Finset.mem_image.mpr ⟨(⟨i, hi⟩, 0), Finset.mem_univ _, (one_mul _).symm⟩

/-- First over-budget Hamming error count in descending order of the four prize rates. -/
def firstBad : Fin 4 → ℕ := ![15, 24, 29, 31]

private abbrev budget : ℕ := 673^16 / 2^128

private theorem budget_cast (L : ℕ∞) :
    (L : ENNReal) ≤ ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card K : ENNReal) ↔
      L ≤ budget := by
  have hε : (prizeThreshold : ℝ≥0) = 1 / 2^128 := by norm_num [prizeThreshold]
  rw [hε, card_K, ← ENNReal.coe_natCast, ← ENNReal.coe_mul]
  induction L using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top, top_le_iff, ENNReal.coe_ne_top, ENat.natCast_ne_top]
  | coe v =>
    have hreal : (v : ℝ≥0) ≤ (1 / 2^128 : ℝ≥0) * (673^16 : ℕ) ↔ v ≤ budget := by
      rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
      exact_mod_cast (Nat.le_div_iff_mul_le (by decide : 0 < 2^128)).symm
    simpa only [ENat.toENNReal_coe, ← ENNReal.coe_natCast, ENNReal.coe_le_coe,
      ENat.natCast_le_natCast] using hreal

private theorem scalar_small_bad (k : ℕ) [NeZero k] (hk : k ≤ 32) :
    (budget : ℕ∞) < Lambda (ReedSolomon.code domain k : Set (H → K))
      (((32-k+1 : ℕ) : ℝ)/32) := by
  have hdist := ReedSolomon.minDist_of_le (α := domain) (n := k) (card_H ▸ hk)
  rw [card_H] at hdist
  have h := FieldListAtMinimumDistance.field_card_le_lambda (ReedSolomon.code domain k)
    (hdist ▸ (show 0 < 32-k+1 by omega))
  rw [hdist, card_H, card_K] at h
  exact lt_of_lt_of_le (by exact_mod_cast (show budget < 673^16 by decide)) h

private theorem scalar_bad (j : Fin 4) :
    (budget : ℕ∞) < Lambda (ReedSolomon.code domain (prizeDimension (ι := H) j) : Set (H → K))
      ((firstBad j : ℝ) / 32) := by
  fin_cases j
  · have h := PrescribedProductList.exceeds_budget domain U Prod.fst (fun _ ↦ rfl)
      (k := 16) (B := budget) (by decide) (by
        rw [card_H, card_U, Nat.choose_eq_descFactorial_div_factorial]; decide)
    rw [card_H] at h
    simpa [prizeDimension, prizeDenominator, card_H, firstBad] using h
  · classical
    have h := ReservedFiberList.list_lower_bound domain inclusion (1 : U) (0 : Fin 1) 8
      (by decide) (by intro i; rw [Fintype.card_fin, pow_one]; rfl)
    rw [card_U, Fintype.card_fin, card_H] at h
    have hb : budget < Nat.choose (32-1) 8 := by
      rw [Nat.choose_eq_descFactorial_div_factorial]
      decide
    have h' := (show (budget : ℕ∞) < (Nat.choose (32-1) 8 : ℕ) by exact_mod_cast hb).trans_le h
    simpa [prizeDimension, prizeDenominator, card_H, firstBad] using h'
  · simpa [prizeDimension, prizeDenominator, card_H, firstBad] using scalar_small_bad 4 (by decide)
  · simpa [prizeDimension, prizeDenominator, card_H, firstBad] using scalar_small_bad 2 (by decide)

/-- The complete real-radius test for all four prize rates, including both grid edges. -/
theorem list_threshold (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code domain (prizeDimension (ι := H) j) : Set (H → K))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card K : ENNReal) ↔
        δ < (firstBad j : ℝ)/32 := by
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  rw [budget_cast]
  constructor
  · intro h
    by_contra! hδ
    have hscalar := (InterleavedListProjection.prize_list_budget_iff (κ := Fin m)
      (ReedSolomon.code domain (prizeDimension (ι := H) j)) δ (by
        rw [Nat.card_eq_fintype_card, card_K]; decide)).mp
      (show _ from by simpa only [Nat.card_eq_fintype_card, card_K] using h)
    rw [Nat.card_eq_fintype_card, card_K] at hscalar
    exact (not_lt_of_ge hscalar) ((scalar_bad j).trans_le (Lambda_mono hδ))
  · intro hδ
    let k := prizeDimension (ι := H) j
    let t := 33 - firstBad j
    have hkt : k ≤ t := by
      fin_cases j <;> norm_num [k, t, prizeDimension, prizeDenominator, card_H, firstBad]
    have ht : (t : ℝ) + firstBad j = 33 := by
      fin_cases j <;> norm_num [t, firstBad]
    have hu := AgreementSubsetListPacking.interleaved_lambda_le_choose_div domain k t m δ hkt
      (by rw [card_H]; norm_num; linarith)
    rw [card_H] at hu
    apply hu.trans
    exact_mod_cast (show Nat.choose 32 k / Nat.choose t k ≤ budget by
      fin_cases j <;>
        simp only [k, t, prizeDimension, prizeDenominator, card_H, firstBad,
          Nat.choose_eq_descFactorial_div_factorial] <;> decide)

/-- An explicit adjacent pair of good and bad grid points for each rate. -/
noncomputable def resolution (j : Fin 4) (m : ℕ) (hm : 0 < m) :
    GrandListResolution (ReedSolomon.code domain (prizeDimension (ι := H) j) : Set (H → K))
      m (prizeThreshold : ℝ≥0) := by
  refine ⟨firstBad j - 1, ?_, ?_, ?_⟩
  · rw [card_H]
    fin_cases j <;> decide
  · apply (list_threshold j m hm _).mpr
    fin_cases j <;> norm_num [gridPt, card_H, firstBad]
  · apply lt_of_not_ge
    intro h
    have hδ := (list_threshold j m hm _).mp h
    fin_cases j <;> norm_num [gridPt, card_H, firstBad] at hδ

/-- The full four-rate grand list prize on this fixed smooth domain at every positive width. -/
theorem listDecodingPrize_all_rates (m : ℕ) (hm : 0 < m) : listDecodingPrize domain m :=
  ⟨hm, PrizeDomainAdmissible.of_smooth domain (by rw [card_H]; decide),
    fun j ↦ (resolution j m hm).to_challenge⟩

#print axioms card_H
#print axioms list_threshold
#print axioms listDecodingPrize_all_rates

end ProximityGap.FourRateList673
