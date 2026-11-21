/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger
import ArkLib.Data.CodingTheory.ProximityGap.MCAStepFunction
import ArkLib.Research.ProximityGap.Frontier._TwoLinePreUnique
import ArkLib.Research.ProximityGap.Frontier._TwoCorePackingThreshold

/-!
# The spike and bisimplex error counts at rate one sixteenth

The two-line estimate and the universal spike construction match below the
unique-decoding boundary. On the boundary, the bisimplex construction
increases the exceptional count from `e+1` to `2e+2`. This gives a whole
interval of field budgets with the same threshold.
-/

open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.TwoLineSpikeThreshold

open TwoCorePackingThreshold (domainLength)
open PrizeShapeRateHalfBracket

private abbrev K : ℕ := 67108864

/-- The complete low-error branch on the smooth production domain. -/
theorem epsMCA_eq_spike {p e : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = domainLength) (he : e ≤ 503316479) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g domainLength (K - 1))
      ((e : ℝ≥0) / domainLength) = ((e + 1 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  classical
  let δ : ℝ≥0 := (e : ℝ≥0) / domainLength
  let dom := KKH26RegimeSplit.powDomain g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg)
  have hej : e + 1 ≤ domainLength := by dsimp [domainLength]; omega
  have he' : e ≤ domainLength := by omega
  apply le_antisymm
  · have hcode : evalCode g domainLength (K - 1) =
        (ReedSolomon.code dom K : Set (Fin domainLength → ZMod p)) := by
      simpa only [dom, show K - 1 + 1 = K by decide] using
        KKH26RegimeSplit.evalCode_eq_reedSolomon g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg)
          (K - 1)
    rw [hcode]
    refine (epsMCA_le_of_badCount_le _ _ (e + 1) ?_).trans (by rw [ZMod.card])
    intro u
    have ht := TwoCorePackingThreshold.agreement_ceiling e he'
    have h := TwoLinePreUnique.production_family_card_le
      (canonicalBadScalarRichPointFamily dom (k := K) δ u (by decide)) (e := e)
      (Fintype.card_fin _) (by change e + (domainLength - e) = domainLength; omega)
      (by decide) (by decide) ht (by dsimp [K, domainLength]; omega)
    simpa only [canonicalBadScalarRichPointFamily, badScalars, δ] using h
  · rw [Ownership.evalCode_pred_eq_rsCode hg (by decide : 0 < K)]
    let positions : Fin (e + 1) ↪ Fin domainLength := Fin.castLEEmb hej
    have h := SpikeFloor.epsMCA_ge_j_div_card (SpikeFloor.rsCode _ K)
      (SpikeFloor.rsCode_noWeightLE (Ownership.smoothDom g domainLength hg)
        (show e + 1 + K ≤ domainLength by dsimp [K, domainLength]; omega))
      (δ := (e : ℝ≥0) / domainLength)
      (by simp [Fintype.card_fin]) (by omega) (by simpa using hej)
      positions (positions.trans dom) (b := (1 : ZMod p)) one_ne_zero
    simpa only [ZMod.card] using h

/-- On the shoulder at or beyond unique decoding, two disjoint simplices attain the
two-core upper bound. -/
theorem epsMCA_eq_bisimplex {p e : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = domainLength) (hlo : 503316480 ≤ e) (hhi : e ≤ 536870911) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g domainLength (K - 1))
      ((e : ℝ≥0) / domainLength) = ((2 * e + 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  have he : e ≤ domainLength := by dsimp [domainLength]; omega
  apply le_antisymm
  · exact TwoCorePackingThreshold.epsMCA_le_twoCore_count hg
      (by decide) (by decide) (by dsimp [domainLength]; omega) (by dsimp [domainLength]; omega)
  · have h := PackingEnvelope.provedPacking_le_epsMCA (d := K - 1) (t := domainLength - e) hg
    have hshoulder : (K - 1) + 2 ≤ domainLength - e ∧ domainLength + 2 ≤ 2 * (domainLength - e) ∧
        2 * (domainLength - e) ≤ domainLength + (K - 1) + 1 := by dsimp [K, domainLength]; omega
    rw [PackingEnvelope.provedPackingCount, ite_eq_left hshoulder,
      show domainLength - (domainLength - e) = e by omega] at h
    have hn : (domainLength : ℝ≥0) ≠ 0 := by norm_num [domainLength]
    have hbound : (e : ℝ≥0) / domainLength ≤ 1 :=
      (div_le_one (pos_iff_ne_zero.mpr hn)).2 (by exact_mod_cast he)
    have hsub : ((domainLength - e : ℕ) : ℝ≥0) / domainLength = 1 - (e : ℝ≥0) / domainLength := by
      rw [Nat.cast_tsub, tsub_div, div_self hn]
    rwa [hsub, tsub_tsub_cancel_of_le hbound] at h

private theorem inv_lt_count {Q p c : ℕ} (hQ : 0 < Q) (hp : 0 < p) (hbudget : p / Q < c) :
    (Q : ℝ≥0∞)⁻¹ < (c : ℝ≥0∞) / (p : ℝ≥0∞) := by
  have hm := (Nat.lt_mul_div_succ p hQ).trans_le (Nat.mul_le_mul_left Q hbudget)
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.ne'
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp0) (Or.inl (ENNReal.natCast_ne_top p)),
    ← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl hQ0) (Or.inl (ENNReal.natCast_ne_top Q))]
  exact_mod_cast (by simpa only [Nat.mul_comm] using hm)

/-- For all integer scalar budgets from 503316480 through 1006632961, the predecessor
fits the budget and the first bisimplex step exceeds it. -/
theorem uniqueDecoding_plateau {p Q : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = domainLength) (hQ : 0 < Q)
    (hlo : 503316480 ≤ p / Q) (hhi : p / Q ≤ 1006632961) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g domainLength (K - 1))
      (Q : ℝ≥0∞)⁻¹ = (15 / 32 : ℝ≥0) := by
  have good := epsMCA_eq_spike (e := 503316479) hg (by decide)
  have bad := epsMCA_eq_bisimplex (e := 503316480) hg (by decide) (by decide)
  have hratio : ((503316480 : ℕ) : ℝ≥0) / domainLength = (15 / 32 : ℝ≥0) := by
    norm_num [domainLength]
  rw [← hratio]
  apply le_antisymm
  · apply mcaDeltaStar_le_of_bad
    rw [bad]
    exact inv_lt_count hQ (Fact.out (p := p.Prime)).pos (by omega)
  · apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good (by decide) (by decide)
    change epsMCA (F := ZMod p) (A := ZMod p) (evalCode g domainLength (K - 1))
      (((503316479 : ℕ) : ℝ≥0) / domainLength) ≤ (Q : ℝ≥0∞)⁻¹
    rw [good]
    apply natCast_div_le_inv_of_mul_le hQ (Fact.out (p := p.Prime)).pos
    exact (Nat.mul_le_mul_right Q hlo).trans (Nat.div_mul_le_self p Q)

#print axioms epsMCA_eq_spike
#print axioms epsMCA_eq_bisimplex
#print axioms uniqueDecoding_plateau

/-- Exact threshold whenever the adjacent integer radii have certified scalar counts on
opposite sides of the field-normalized budget. -/
private theorem adjacent_counts {p j Q a b : ℕ} [Fact p.Prime] {g : ZMod p}
    (hj : 1 ≤ j) (hjn : j ≤ domainLength) (hQ : 0 < Q)
    (hprev : epsMCA (F := ZMod p) (A := ZMod p) (evalCode g domainLength (K - 1))
      (((j - 1 : ℕ) : ℝ≥0) / domainLength) = (a : ℝ≥0∞) / (p : ℝ≥0∞))
    (hnext : epsMCA (F := ZMod p) (A := ZMod p) (evalCode g domainLength (K - 1))
      ((j : ℝ≥0) / domainLength) = (b : ℝ≥0∞) / (p : ℝ≥0∞))
    (ha : a ≤ p / Q) (hb : p / Q < b) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g domainLength (K - 1))
      (Q : ℝ≥0∞)⁻¹ = (j : ℝ≥0) / domainLength := by
  apply le_antisymm
  · apply mcaDeltaStar_le_of_bad
    rw [hnext]
    exact inv_lt_count hQ (Fact.out (p := p.Prime)).pos hb
  · apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good hj hjn
    rw [predecessorRadius, hprev]
    exact natCast_div_le_inv_of_mul_le hQ (Fact.out (p := p.Prime)).pos
      ((Nat.mul_le_mul_right Q ha).trans (Nat.div_mul_le_self p Q))

/-- Across the three budget regimes the exact error index is
`min B (max 503316480 (B/2))`, where `B=⌊p/2^128⌋`. -/
theorem rateSixteenth_threshold_curve {p B : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = domainLength) (hB : B = p / 2 ^ 128)
    (hpos : 1 ≤ B) (hmax : B ≤ 1295252617) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g domainLength (K - 1))
      (ProximityGap.epsStar : ℝ≥0∞) =
        ((min B (max 503316480 (B / 2)) : ℕ) : ℝ≥0) / domainLength := by
  by_cases hlow : B ≤ 503316479
  · rw [max_eq_left (by omega : B/2 ≤ 503316480), min_eq_left (by omega : B ≤ 503316480),
      epsStar_coe_eq_natCast_inv]
    exact adjacent_counts hpos (by dsimp [domainLength]; omega) (by norm_num)
      (epsMCA_eq_spike (e := B - 1) hg (by omega))
      (epsMCA_eq_spike (e := B) hg hlow)
      (by omega) (by omega)
  by_cases hmid : B ≤ 1006632961
  · rw [max_eq_left (by omega : B/2 ≤ 503316480), min_eq_right (by omega : 503316480 ≤ B)]
    have h := uniqueDecoding_plateau (Q := 2 ^ 128) hg (by norm_num) (by omega) (by omega)
    rw [epsStar_coe_eq_natCast_inv, h]
    norm_num [domainLength]
  rw [max_eq_right (by omega : 503316480 ≤ B/2), min_eq_right (by omega : B/2 ≤ B)]
  by_cases hshoulder : B / 2 ≤ 536870911
  · rw [epsStar_coe_eq_natCast_inv]
    apply adjacent_counts (j := B / 2) (by omega) (by dsimp [domainLength]; omega) (by norm_num)
      (epsMCA_eq_bisimplex (e := B / 2 - 1) hg (by omega) (by omega))
      (epsMCA_eq_bisimplex (e := B / 2) hg (by omega) hshoulder)
      (by omega) (by omega)
  · rw [hB]
    exact TwoCorePackingThreshold.rateSixteenth_window hg (by omega) (by omega)

#print axioms rateSixteenth_threshold_curve

/-- The budget holds exactly on this open interval of real radii. The endpoint itself
already exceeds the budget. -/
theorem rateSixteenth_good_iff {p B : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = domainLength) (hB : B = p / 2 ^ 128)
    (hpos : 1 ≤ B) (hmax : B ≤ 1295252617) (δ : ℝ≥0) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g domainLength (K - 1)) δ ≤
      (ProximityGap.epsStar : ℝ≥0∞) ↔
      δ < ((min B (max 503316480 (B / 2)) : ℕ) : ℝ≥0) / domainLength := by
  have hcurve := rateSixteenth_threshold_curve hg hB hpos hmax
  have hindex : min B (max 503316480 (B / 2)) < domainLength := by
    dsimp [domainLength]
    omega
  have hlt : mcaDeltaStar (F := ZMod p) (A := ZMod p)
      (evalCode g domainLength (K - 1)) (ProximityGap.epsStar : ℝ≥0∞) < 1 := by
    rw [hcurve, div_lt_one (by norm_num [domainLength])]
    exact_mod_cast hindex
  rw [← hcurve]
  constructor
  · intro h
    by_contra! hle
    have hbad := MCAStepFunction.lt_epsMCA_mcaDeltaStar_of_lt_one _ _ hlt
    exact hbad.not_ge ((epsMCA_mono _ hle).trans h)
  · intro h
    by_contra! hbad
    exact h.not_ge (mcaDeltaStar_le_of_bad _ _ hbad)

/-- The good-radius interval holds at every positive interleaving width. -/
theorem rateSixteenth_interleaved_good_iff {p B : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = domainLength) (hB : B = p / 2 ^ 128)
    (hpos : 1 ≤ B) (hmax : B ≤ 1295252617) (width : ℕ) [NeZero width] (δ : ℝ≥0) :
    epsMCA (F := ZMod p) (A := Fin width → ZMod p)
      ((evalCode g domainLength (K - 1)) ^⋈ (Fin width)) δ ≤ (ProximityGap.epsStar : ℝ≥0∞) ↔
      δ < ((min B (max 503316480 (B / 2)) : ℕ) : ℝ≥0) / domainLength := by
  have hcode := Ownership.evalCode_pred_eq_rsCode hg (by decide : 0 < K)
  rw [hcode, epsMCA_interleaved_eq, ← hcode]
  exact rateSixteenth_good_iff hg hB hpos hmax δ

/-- Every positive interleaving width has the same explicit operational supremum. -/
theorem rateSixteenth_interleaved_threshold_curve {p B : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = domainLength) (hB : B = p / 2 ^ 128)
    (hpos : 1 ≤ B) (hmax : B ≤ 1295252617) (width : ℕ) [NeZero width] :
    mcaDeltaStar (F := ZMod p) (A := Fin width → ZMod p)
      ((evalCode g domainLength (K - 1)) ^⋈ (Fin width)) (ProximityGap.epsStar : ℝ≥0∞) =
      ((min B (max 503316480 (B / 2)) : ℕ) : ℝ≥0) / domainLength := by
  have hcode := Ownership.evalCode_pred_eq_rsCode hg (by decide : 0 < K)
  rw [hcode, mcaDeltaStar_interleaved_eq, ← hcode]
  exact rateSixteenth_threshold_curve hg hB hpos hmax

#print axioms rateSixteenth_good_iff
#print axioms rateSixteenth_interleaved_good_iff
#print axioms rateSixteenth_interleaved_threshold_curve

end ArkLib.ProximityGap.Frontier.TwoLineSpikeThreshold
