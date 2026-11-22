/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSliceThreshold
import ArkLib.Research.ProximityGap.Frontier.TwoErrorDomain237

/-! # Four exact 128-site list thresholds from a two-error slice certificate -/
namespace ProximityGap.TwoErrorSliceThreshold

open Code GrandChallenges
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
  [Field F] [DecidableEq F] [Fintype F]

private abbrev budget (K : Type) [Fintype K] := Fintype.card K / 2^128

/-- In this field-size range, the half-rate slice and ordinary sample packing at
the lower rates determine all real-radius thresholds at every positive width. -/
theorem four_thresholds (D : I ↪ F) (cert : TwoErrorSlice.PenaltyBound D)
    (hn : Fintype.card I=128) (H : Subgroup Fˣ) [Fintype H] (z : I → H)
    (hz : ∀ i, D i=((z i : Fˣ) : F)) (hH : Fintype.card H=128)
    (upper : 361269899996423739323753777598085 ≤ budget F)
    (lower : 128 * budget F < Nat.choose 128 65) (pairs : (budget F+1).choose 2 ≤ Nat.card F)
    (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → F))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card F : ENNReal) ↔
        δ < (FourRateList128.firstBad j : ℝ)/128 := by
  rw [FourRateList128.budget_cast]
  by_cases hhalf : j=0
  · subst j
    simpa [budget,prizeDimension, prizeDenominator,hn,FourRateList128.firstBad] using
      TwoErrorSlice.half_threshold D cert hn H z hz (budget F) upper (hH ▸ lower) pairs m hm δ
  let k := prizeDimension (ι := I) j
  let e := FourRateList128.firstBad j
  have hk : 0 < k ∧ k ≤ 128 := by
    fin_cases j <;> norm_num [k,prizeDimension,prizeDenominator,hn]
  have he : 128-k+1=e := by
    fin_cases j <;> simp_all [k,e,prizeDimension,prizeDenominator,FourRateList128.firstBad]
  have pack : (Nat.choose 128 k) ≤ budget F := by
    apply le_trans _ upper
    fin_cases j
    · exact False.elim (hhalf rfl)
    all_goals simp only [k,prizeDimension,prizeDenominator,hn,Nat.choose_eq_descFactorial_div_factorial]; decide
  let : NeZero k := ⟨Nat.ne_of_gt hk.1⟩
  constructor
  · intro good
    by_contra! hδ
    have hd := ReedSolomon.minDist_of_le (α := D) (n := k) (hn ▸ hk.2)
    rw [hn,he] at hd
    have hpos : 0<e := by omega
    have large := FieldListAtMinimumDistance.field_card_le_lambda (ReedSolomon.code D k)
      (hd ▸ hpos)
    rw [hd,hn] at large
    let diag : F → Fin m → F := fun x _ => x
    have hi : Function.Injective diag := fun _ _ h => congrFun h ⟨0,hm⟩
    have hdg := Lambda_le_of_injective_comp (e := diag) hi
      (C := (ReedSolomon.code D k : Set (I → F)))
      (D := interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F)))
      (fun _ hx _ => hx) δ
    have small : budget F < Fintype.card F := Nat.div_lt_self Fintype.card_pos (by decide)
    exact (not_lt_of_ge (hdg.trans good))
      ((show (budget F : ℕ∞) < Fintype.card F by exact_mod_cast small).trans_le
        (large.trans (Lambda_mono hδ)))
  · intro hδ
    have hkr : (k : ℝ) + e = 129 := by exact_mod_cast (show k+e=129 by omega)
    have hu := AgreementSubsetListPacking.interleaved_lambda_le_choose_div D k k m δ le_rfl
      (by rw [hn]; norm_num; change δ < (e : ℝ)/128 at hδ; linarith)
    rw [hn,Nat.choose_self,Nat.div_one] at hu
    exact hu.trans (by exact_mod_cast pack)

/-- Exact scalar and interleaved thresholds for the 237-bit subgroup from
its computed cross-ratio histogram. -/
theorem thresholds237 (cert : TwoErrorSlice.PenaltyBound domain237) (j : Fin 4)
    (m : ℕ) (hm : 0<m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code domain237 (prizeDimension (ι := Fin 128) j) : Set (Fin 128 → ZMod ArkLib.ProximityGap.Frontier.DyadicLogWitness237.P))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) *
        (Fintype.card (ZMod ArkLib.ProximityGap.Frontier.DyadicLogWitness237.P) : ENNReal) ↔
        δ < (FourRateList128.firstBad j : ℝ)/128 := by
  let P := ArkLib.ProximityGap.Frontier.DyadicLogWitness237.P
  have hupper : 361269899996423739323753777598085 ≤ budget (ZMod P) := by
    rw [budget,ZMod.card]; decide
  have hlower : 128*budget (ZMod P) < Nat.choose 128 65 := by
    rw [budget,ZMod.card,Nat.choose_eq_descFactorial_div_factorial]; decide
  have hpairs : (budget (ZMod P)+1).choose 2 ≤ Nat.card (ZMod P) := by
    rw [budget,Nat.card_eq_fintype_card,ZMod.card,Nat.choose_two_right]; decide
  exact four_thresholds domain237 cert (Fintype.card_fin 128) group237 index237
    index237_value group237_card hupper hlower hpairs j m hm δ

/-- The list prize on all four rates for the specified field, conditional only
on the finite cross-ratio histogram for its own evaluation sites. -/
theorem prize237 (cert : TwoErrorSlice.PenaltyBound domain237) (m : ℕ) (hm : 0<m) :
    listDecodingPrize domain237 m := by
  have threshold := thresholds237 cert
  refine ⟨hm,PrizeDomainAdmissible.of_smooth domain237 (by rw [Fintype.card_fin]; decide),?_⟩
  intro j
  apply GrandListResolution.to_challenge
  refine ⟨FourRateList128.firstBad j - 1,?_,?_,?_⟩
  · rw [Fintype.card_fin]; fin_cases j <;> decide
  · apply (threshold j m hm _).mpr
    fin_cases j <;> norm_num [gridPt,FourRateList128.firstBad]
  · apply lt_of_not_ge
    intro h
    have hδ := (threshold j m hm _).mp h
    fin_cases j <;> norm_num [gridPt,FourRateList128.firstBad] at hδ

end ProximityGap.TwoErrorSliceThreshold

#print axioms ProximityGap.TwoErrorSliceThreshold.four_thresholds
#print axioms ProximityGap.TwoErrorSliceThreshold.prize237
