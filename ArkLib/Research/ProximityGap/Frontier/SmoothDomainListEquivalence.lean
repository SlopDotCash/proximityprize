/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSlicePrize128
import ArkLib.ToMathlib.InformationTheory.Hamming

/-! # Exact list sizes on smooth domains of equal length -/

namespace ProximityGap.SmoothDomainListEquivalence

open Code GrandChallenges
open scoped NNReal ENNReal

private theorem lambda_reindex {I J A : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (C : Set (J → A)) (D : Set (I → A)) (hd : ∀ w ∈ C, w ∘ e ∈ D) (δ : ℝ) :
    Lambda C δ ≤ Lambda D δ := by
  classical
  apply Lambda_le_iff_forall_encard_le.mpr
  intro W
  apply le_trans _ (encard_closeCodewordsRel_le_Lambda D δ (W ∘ e))
  have hin : (closeCodewordsRel C W δ).InjOn (fun w => w ∘ e) :=
    fun w _ v _ h => funext fun j => by simpa using congrFun h (e.symm j)
  rw [← hin.encard_image]
  apply Set.encard_mono
  rintro _ ⟨w,hw,rfl⟩
  obtain ⟨hc,hδ⟩ := mem_closeCodewordsRel_iff.mp hw
  refine mem_closeCodewordsRel_iff.mpr ⟨hd w hc,?_⟩
  rw [relHammingDist_coe, hammingDist_comp_equiv, Fintype.card_congr e, ← relHammingDist_coe]
  exact hδ

/-- The entire worst-center list profile agrees after scaling and reindexing
between any two smooth evaluation domains of equal size in a field. -/
theorem interleaved_eq {I J F : Type} [Fintype I] [Fintype J] [Field F] [DecidableEq F]
    (D : I ↪ F) (E : J ↪ F) [ReedSolomon.Smooth D] [ReedSolomon.Smooth E]
    (hn : Fintype.card I=Fintype.card J) (k m : ℕ) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))) δ =
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code E k : Set (J → F))) δ := by
  obtain ⟨e,a,he⟩ := SmoothDomainMcaEquivalence.exists_reindex_scale D E hn
  have hb (j : J) : E j = (↑a⁻¹ : F) * D (e.symm j) := by
    rw [he,Equiv.apply_symm_apply,←mul_assoc,Units.inv_mul,one_mul]
  apply le_antisymm
  · apply lambda_reindex e.symm
    intro w hw i
    exact SmoothDomainMcaEquivalence.mem_code_scale e.symm a⁻¹ hb (hw i)
  · apply lambda_reindex e
    intro w hw i
    exact SmoothDomainMcaEquivalence.mem_code_scale e a he (hw i)

open ArkLib.ProximityGap.Frontier.DyadicLogWitness237 (P)
open TwoErrorSliceThreshold

/-- A single order-128 histogram suffices for every order-128 smooth
domain and coset in the field of order P. -/
theorem smooth237_thresholds {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (D : I ↪ ZMod P) [ReedSolomon.Smooth D] (hn : Fintype.card I=128)
    (cert : TwoErrorSlice.PenaltyBound domain237) (j : Fin 4) (m : ℕ) (hm : 0<m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → ZMod P))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card (ZMod P) : ENNReal) ↔
        δ < (FourRateList128.firstBad j : ℝ)/128 := by
  have heqCard : Fintype.card I = Fintype.card (Fin 128) := hn.trans (Fintype.card_fin _).symm
  rw [interleaved_eq D domain237 heqCard]
  have hdim : prizeDimension (ι := I) j = prizeDimension (ι := Fin 128) j := by
    simp only [prizeDimension,heqCard]
  rw [hdim]
  exact thresholds237 cert j m hm δ

/-- The four-rate list-decoding prize on every smooth 128-site domain over the
237-bit prime field. -/
theorem smooth237_prize {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (D : I ↪ ZMod P) [ReedSolomon.Smooth D] (hn : Fintype.card I=128)
    (cert : TwoErrorSlice.PenaltyBound domain237) (m : ℕ) (hm : 0<m) :
    listDecodingPrize D m := by
  refine ⟨hm,PrizeDomainAdmissible.of_smooth D (by rw [hn]; decide),?_⟩
  intro j
  apply GrandListResolution.to_challenge
  refine ⟨FourRateList128.firstBad j - 1,?_,?_,?_⟩
  · rw [hn]; fin_cases j <;> decide
  · apply (smooth237_thresholds D hn cert j m hm _).mpr
    fin_cases j <;> norm_num [gridPt,hn,FourRateList128.firstBad]
  · apply lt_of_not_ge
    intro h
    have hδ := (smooth237_thresholds D hn cert j m hm _).mp h
    fin_cases j <;> norm_num [gridPt,hn,FourRateList128.firstBad] at hδ

end ProximityGap.SmoothDomainListEquivalence

#print axioms ProximityGap.SmoothDomainListEquivalence.interleaved_eq
#print axioms ProximityGap.SmoothDomainListEquivalence.smooth237_prize
