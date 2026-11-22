/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainListEquivalence
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSliceNormalize
import Mathlib.FieldTheory.Finite.Basic

/-! # Four exact list thresholds on smooth 128-site domains in a prime band -/

namespace ProximityGap.TwoErrorPrimeBand

open Code GrandChallenges TwoErrorSlice
open scoped NNReal ENNReal

set_option exponentiation.threshold 512

/-- The budget pays for all lists through 62 errors and is exceeded by the
prescribed-product construction at 63 errors. -/
def InBand (p : ℕ) : Prop :=
  361269899996423739323753777598085 ≤ p / 2^128 ∧
    128*(p / 2^128) < Nat.choose 128 65

private theorem sizes {p : ℕ} (band : InBand p) :
    128 < p ∧ 2^448 < p^2 ∧ ((p / 2^128)+1).choose 2 ≤ p := by
  let B := p / 2^128
  have hB : B * 2^128 ≤ p := Nat.div_mul_le_self _ _
  have pmin := (Nat.mul_le_mul_right (2^128) band.1).trans hB
  have hp : 128 < 361269899996423739323753777598085 * 2^128 := by decide
  have hl : 2^448 < (361269899996423739323753777598085 * 2^128)^2 := by decide
  have hnum : Nat.choose 128 65 ≤ 128*2^128 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have hcap : B+1 ≤ 2^128 := by
    have := band.2.trans_le hnum
    change 128*B < 128*2^128 at this
    omega
  refine ⟨hp.trans_le pmin,hl.trans_le (Nat.pow_le_pow_left pmin 2),?_⟩
  change (B+1).choose 2 ≤ p
  rw [Nat.choose_two_right,Nat.add_sub_cancel]
  apply (Nat.div_le_self _ _).trans
  rw [Nat.mul_comm (B+1) B]
  exact (Nat.mul_le_mul_left B hcap).trans hB

variable {F : Type} [Field F] [NeZero (128:F)]
variable (E : Fin 128 ↪ F) (w : F) (hw : IsPrimitiveRoot w 128)
  (hE : ∀ i, E i=w^(i : ℕ))
  (rows : ∀ d : Fin 128, StandardRow d → RowPenaltyBound E 0 d)

include hw hE rows in
/-- Within this numerical prime band, the same six auxiliary rows give the
exact sponsor threshold for every smooth 128-site domain and every width. -/
theorem smooth_thresholds_of_six {p : ℕ} [Fact p.Prime] (band : InBand p)
    {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=128)
    (j : Fin 4) (m : ℕ) (hm : 0<m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → ZMod p))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card (ZMod p) : ENNReal) ↔
        δ < (FourRateList128.firstBad j : ℝ)/128 := by
  classical
  obtain ⟨hp,large,pairs⟩ := sizes band
  let : NeZero (128 : ZMod p) := ⟨fun h =>
    hp.not_ge (Nat.le_of_dvd (by decide : 0<128) ((ZMod.natCast_eq_zero_iff 128 p).mp h))⟩
  let H := ReedSolomon.Smooth.H D
  obtain ⟨c,_⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  let : Fintype H := Fintype.ofEquiv I c
  have cH : Fintype.card H = 128 := (Fintype.card_congr c).symm.trans hn
  obtain ⟨a,ha⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := H)).mp inferInstance
  let z := ((a : (ZMod p)ˣ) : ZMod p)
  have hz : IsPrimitiveRoot z 128 := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    change orderOf ((a : (ZMod p)ˣ) : ZMod p)=128
    rw [orderOf_units,Subgroup.orderOf_coe,ha,Nat.card_eq_fintype_card,cH]
  let power : Fin 128 ↪ ZMod p :=
    ⟨fun i => z^(i : ℕ), fun i k h => Fin.ext (hz.pow_inj i.isLt k.isLt h)⟩
  have cert := penaltyBound_of_six power E z w hz hw (fun _ => rfl) hE large rows
  let idx (i : Fin 128) : H := a^(i : ℕ)
  have inj : Function.Injective idx := fun _ _ h => power.injective
    (congrArg (fun b : H => ((b : (ZMod p)ˣ) : ZMod p)) h)
  let e := Equiv.ofBijective idx ((Fintype.bijective_iff_injective_and_card idx).mpr
    ⟨inj,(Fintype.card_fin _).trans cH.symm⟩)
  let G := FourRateList128.domain H
  have eval (i : H) : power (e.symm i) = G i := by
    exact congrArg (fun b : H => ((b : (ZMod p)ˣ) : ZMod p)) (e.apply_symm_apply i)
  have cert' : PenaltyBound G := by
    apply penaltyBound_transfer G power e.symm.toEmbedding _ _ cert
    · intro u v _ h
      simpa only [Equiv.coe_toEmbedding,eval] using h
    · intro u v _ _ x _ y _ A _ B _ h
      simpa only [ratio,Equiv.coe_toEmbedding,eval] using h
  let : ReedSolomon.Smooth G := FourRateList128.smooth H cH
  have same : Fintype.card I=Fintype.card H := hn.trans cH.symm
  rw [SmoothDomainListEquivalence.interleaved_eq D G same]
  have dim : prizeDimension (ι := I) j=prizeDimension (ι := H) j := by
    simp only [prizeDimension,same]
  rw [dim]
  apply TwoErrorSliceThreshold.four_thresholds G cert' cH H id (fun _ => rfl) cH
  · change _ ≤ Fintype.card (ZMod p)/2^128
    simpa only [ZMod.card] using band.1
  · change 128*(Fintype.card (ZMod p)/2^128) < _
    simpa only [ZMod.card] using band.2
  · change (Fintype.card (ZMod p)/2^128+1).choose 2 ≤ Nat.card (ZMod p)
    simpa only [Nat.card_eq_fintype_card,ZMod.card] using pairs
  · exact hm

include hw hE rows in
/-- The list-decoding prize follows for every positive interleaving width. -/
theorem smooth_prize_of_six {p : ℕ} [Fact p.Prime] (band : InBand p)
    {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=128)
    (m : ℕ) (hm : 0<m) : listDecodingPrize D m := by
  have threshold := smooth_thresholds_of_six E w hw hE rows band D hn
  refine ⟨hm,PrizeDomainAdmissible.of_smooth D (by rw [hn]; decide),?_⟩
  intro j
  apply GrandListResolution.to_challenge
  refine ⟨FourRateList128.firstBad j - 1,?_,?_,?_⟩
  · rw [hn]; fin_cases j <;> decide
  · apply (threshold j m hm _).mpr
    fin_cases j <;> norm_num [gridPt,hn,FourRateList128.firstBad]
  · apply lt_of_not_ge
    intro h
    have hδ := (threshold j m hm _).mp h
    fin_cases j <;> norm_num [gridPt,hn,FourRateList128.firstBad] at hδ

open ArkLib.ProximityGap.Frontier.DyadicLogWitness237 (P)

/-- The certified 237-bit prime is in the exact-threshold band. -/
theorem inBand237 : InBand P := by
  unfold InBand
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide

include hw hE rows in
/-- Sharp thresholds on every smooth 128-site domain in the 237-bit field. -/
theorem smooth237_thresholds_of_six {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (D : I ↪ ZMod P) [ReedSolomon.Smooth D] (hn : Fintype.card I=128)
    (j : Fin 4) (m : ℕ) (hm : 0<m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → ZMod P))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card (ZMod P) : ENNReal) ↔
        δ < (FourRateList128.firstBad j : ℝ)/128 :=
  smooth_thresholds_of_six E w hw hE rows inBand237 D hn j m hm δ

include hw hE rows in
theorem smooth237_prize_of_six {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (D : I ↪ ZMod P) [ReedSolomon.Smooth D] (hn : Fintype.card I=128)
    (m : ℕ) (hm : 0<m) : listDecodingPrize D m :=
  smooth_prize_of_six E w hw hE rows inBand237 D hn m hm

end ProximityGap.TwoErrorPrimeBand

#print axioms ProximityGap.TwoErrorPrimeBand.smooth_thresholds_of_six
#print axioms ProximityGap.TwoErrorPrimeBand.smooth_prize_of_six
#print axioms ProximityGap.TwoErrorPrimeBand.smooth237_prize_of_six
