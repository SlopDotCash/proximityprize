/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Research.ProximityGap.Frontier.AgreementSubsetListPacking
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection
import ArkLib.Research.ProximityGap.Frontier.ListScalarExtension
import ArkLib.Research.ProximityGap.Frontier.PrescribedProductList
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum.Prime

/-! # A rate-quarter list threshold over a degree-27 extension of the Fermat prime field

The 128 evaluation points belong to the prime subfield. Prescribing two coefficients of
the degree-34 locator there yields a scalar list larger than the extension-field budget.
Every list with at least 35 agreements satisfies the budget by incidence counting.
-/

namespace ProximityGap.SubfieldQuarterListThreshold

open Code GrandChallenges
open scoped NNReal ENNReal

instance : Fact (Nat.Prime 257) := ⟨by norm_num⟩

/-- The ambient field for the 128-bit list budget. -/
abbrev E := GaloisField 257 27

noncomputable instance : Fintype E := Fintype.ofFinite _
noncomputable instance : DecidableEq E := Classical.decEq _

theorem card_E : Fintype.card E = 257 ^ 27 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 257 27 (by decide)

/-- Nine generates the subgroup of squares in the prime subfield. -/
def generator : (ZMod 257)ˣ := Units.mk0 9 (by decide)

theorem generator_order : orderOf generator = 128 := by
  have hhalf : (9 : ZMod 257) ^ (2 : ℕ)^6 ≠ 1 := by decide
  have hfull : (9 : ZMod 257) ^ (2 : ℕ)^7 = 1 := by decide
  rw [← orderOf_injective (Units.coeHom (ZMod 257)) Units.val_injective generator]
  exact orderOf_eq_prime_pow (x := (9 : ZMod 257)) hhalf hfull

/-- Each coordinate is one of the 128 prime-subfield squares. -/
abbrev H := Subgroup.zpowers generator

noncomputable instance : Fintype H := Fintype.ofFinite H

theorem card_H : Fintype.card H = 128 := by
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_zpowers _).trans generator_order

/-- The prime-field evaluation embedding. -/
def baseDomain : H ↪ ZMod 257 :=
  ⟨fun i ↦ ((i : (ZMod 257)ˣ) : ZMod 257), fun _ _ he ↦ Subtype.ext (Units.ext he)⟩

/-- The evaluation points viewed in the degree-27 extension. -/
noncomputable def domain : H ↪ E :=
  baseDomain.trans ⟨algebraMap (ZMod 257) E, (algebraMap (ZMod 257) E).injective⟩

noncomputable instance smoothDomain : ReedSolomon.Smooth domain where
  H := H.map (Units.map (algebraMap (ZMod 257) E).toMonoidHom)
  a := 1
  h_card_pow2 := ⟨7, card_H⟩
  h_coset := by
    classical
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨_, ⟨i.val, i.property, rfl⟩, one_mul _⟩
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, (one_mul _).symm⟩

/-- Integer list budget for the extension alphabet at 128 bits of security. -/
abbrev B : ℕ := 257 ^ 27 / 2^128

private theorem budget_cast (l : ℕ∞) :
    (l : ENNReal) ≤ ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card E : ENNReal) ↔
      l ≤ B := by
  have hε : (prizeThreshold : ℝ≥0) = 1 / 2^128 := by norm_num [prizeThreshold]
  have hlo : (B : ℝ≥0) ≤ (1 / 2^128 : ℝ≥0) * (257 ^ 27 : ℕ) := by
    norm_num [B]
    rw [le_div_iff₀ (by positivity)]
    norm_num
  have hhi : (1 / 2^128 : ℝ≥0) * (257 ^ 27 : ℕ) < ((B + 1 : ℕ) : ℝ≥0) := by norm_num [B]
  have hl : (B : ENNReal) ≤ ((1 / 2^128 : ℝ≥0) : ENNReal) * (257 ^ 27 : ℕ) := by exact_mod_cast hlo
  have hu : ((1 / 2^128 : ℝ≥0) : ENNReal) * (257 ^ 27 : ℕ) < ((B + 1 : ℕ) : ENNReal) := by exact_mod_cast hhi
  rw [hε, card_E]
  constructor
  · intro h
    have hlt : l < ((B+1 : ℕ) : ℕ∞) := by exact_mod_cast (h.trans_lt hu)
    induction l using ENat.recTopCoe with
    | top => simp at hlt
    | coe n =>
      exact_mod_cast (Nat.le_of_lt_succ (show n < B + 1 by exact_mod_cast hlt))
  · intro h
    exact (show (l : ENNReal) ≤ B by exact_mod_cast h).trans hl

/-- The closed-ball prize budget holds at every positive width exactly below 47/64. -/
theorem rateQuarter (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code domain 32 : Set (H → E))) δ :
      ENNReal) ≤ ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card E : ENNReal) ↔
        δ < (47 : ℝ) / 64 := by
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  rw [budget_cast]
  constructor
  · intro h
    by_contra! hδ
    have hscalar := (InterleavedListProjection.prize_list_budget_iff
      (κ := Fin m) (ReedSolomon.code domain 32) δ (by
        rw [Nat.card_eq_fintype_card, card_E]; decide)).mp
        (show _ from (by simpa only [Nat.card_eq_fintype_card, card_E] using h))
    have hlower := PrescribedProductList.exceeds_budget_deeper baseDomain H id (fun _ ↦ rfl)
      1 (k := 32) (B := B) (by decide) (by
        rw [card_H, ZMod.card, Nat.choose_eq_descFactorial_div_factorial]; decide)
    have hext := hlower.trans_le (ListScalarExtension.lambda_le (algebraMap (ZMod 257) E) baseDomain 32 _)
    rw [card_H] at hext
    rw [Nat.card_eq_fintype_card, card_E] at hscalar
    apply (not_lt_of_ge hscalar)
    apply hext.trans_le
    exact Lambda_mono (by norm_num; linarith)
  · intro hδ
    have hu := AgreementSubsetListPacking.interleaved_lambda_le_choose_div domain 32 35 m δ
      (by decide) (by rw [card_H]; norm_num; linarith)
    rw [card_H] at hu
    apply hu.trans
    exact_mod_cast (show Nat.choose 128 32 / Nat.choose 35 32 ≤ B by
      simp only [Nat.choose_eq_descFactorial_div_factorial]; decide)

/-- The final safe integer Hamming radius is 93. -/
noncomputable def rateQuarterResolution (m : ℕ) (hm : 0 < m) :
    GrandListResolution (ReedSolomon.code domain 32 : Set (H → E)) m
      (prizeThreshold : ℝ≥0) := by
  refine ⟨93, by rw [card_H]; decide, ?_, ?_⟩
  · apply (rateQuarter m hm _).mpr
    norm_num [gridPt, card_H]
  · apply lt_of_not_ge
    intro h
    have hn := (rateQuarter m hm (gridPt (ι := H) (93+1) : ℝ)).mp h
    norm_num [gridPt, card_H] at hn

/-- The official smooth-domain list challenge at prize index one. -/
theorem grandListDecodingChallengeRs_rateQuarter (m : ℕ) (hm : 0 < m) :
    grandListDecodingChallengeRs domain (prizeDimension (ι := H) 1) m
      (prizeThreshold : ℝ≥0) := by
  have hk : prizeDimension (ι := H) 1 = 32 := by
    norm_num [prizeDimension, prizeDenominator, card_H]
  rw [hk]
  exact (rateQuarterResolution m hm).to_challenge

#print axioms generator_order
#print axioms rateQuarter
#print axioms grandListDecodingChallengeRs_rateQuarter

end ProximityGap.SubfieldQuarterListThreshold
