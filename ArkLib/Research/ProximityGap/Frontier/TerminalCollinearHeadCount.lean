/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadDeterminantCover
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeConditionedThreshold
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateQuarterPrimitiveDirection
import ArkLib.Research.ProximityGap.Frontier._FSMB_CoreAbsorptionLadder

/-! # Distinct bad scalars on collinear heads at the second-prime predecessor

At a covered coordinate, all fresh agreements on collinear polynomial heads
use one scalar. At an uncovered coordinate each head supplies at most one.
The count uses the actual no-joint clause of the MCA bad-event family.
-/

open Finset Polynomial Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCollapsedClusterInjection
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirection
open scoped NNReal

namespace ProximityGap.TerminalCollinearHeadCount

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
variable {dom : I ↪ F} {k : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- Count the actual bad scalars on a family of collinear polynomial secants, including
uncovered coordinates. Every scalar on these heads has a fresh agreement. -/
theorem collinear_card (fam : BadScalarRichPointFamily dom k δ u) (H : Finset (LineParameter F))
    (hH : H ⊆ lineParameters fam) (a b : LineParameter F) (hab : a ≠ b)
    (hdet : ∀ c ∈ H, lineDeterminant a b c = 0) :
    let U := H.biUnion fun c => jointCore dom (u 0) (u 1) c.1 c.2
    (H.biUnion (pointsOn fam)).card ≤ U.card + (Fintype.card I - U.card)*H.card := by
  classical
  let core (c : LineParameter F) := jointCore dom (u 0) (u 1) c.1 c.2
  let U := H.biUnion core
  let covered := fun i => primitiveScalarAt a b (dom i)
  let outside (p : I × LineParameter F) :=
    (u 0 p.1 - p.2.1.eval (dom p.1)) / (p.2.2.eval (dom p.1) - u 1 p.1)
  have hsub : H.biUnion (pointsOn fam) ⊆
      U.image covered ∪ ((univ \ U) ×ˢ H).image outside := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := mem_biUnion.mp hz
    obtain ⟨hzG, hq⟩ := (mem_pointsOn_iff fam c z).mp hzc
    obtain ⟨hdegA, hdegB⟩ := lineParameter_degree_lt fam (hH hc)
    have hnot := not_subset_jointCore_of_not_pairJointAgreesOn dom (u 0) (u 1)
      _ c.1 c.2 hdegA hdegB (fam.noJoint z hzG)
    obtain ⟨x, hx, hxout⟩ := Finset.not_subset.mp hnot
    rw [hq] at hx
    by_cases hxU : x ∈ U
    · obtain ⟨w, hw, hxw⟩ := mem_biUnion.mp hxU
      have htrans := transverse_of_mem_fullAgreement_mem_targetCore_not_mem_sourceCore
        dom (u 0) (u 1) c w z hx hxw hxout
      have heq := pairEquation_of_mem_fullAgreement_of_mem_jointCore dom (u 0) (u 1) c w z hx hxw
      have hprim := gamma_eq_primitiveScalarAt_of_pairEquation a b c w hab
        (hdet c hc) (hdet w hw) htrans heq
      exact mem_union_left _ (mem_image.mpr ⟨x, hxU, hprim.symm⟩)
    · simp only [fullAgreement, mem_filter, mem_univ, true_and, eval_add, eval_mul, eval_C] at hx
      have hd : c.2.eval (dom x) - u 1 x ≠ 0 := by
        intro he
        have hzero := sub_eq_zero.mp he
        apply hxout
        simp only [jointCore, mem_filter, mem_univ, true_and]
        exact ⟨by rw [hzero] at hx; exact add_right_cancel hx, hzero⟩
      have hlabel : z = outside (x,c) := by
        change z = _ / _
        apply (eq_div_iff hd).mpr
        linear_combination hx
      exact mem_union_right _ (mem_image.mpr ⟨(x,c), mem_product.mpr
        ⟨mem_sdiff.mpr ⟨mem_univ x,hxU⟩, hc⟩, hlabel.symm⟩)
  have hsum := (card_le_card hsub).trans (card_union_le _ _)
  have h := hsum.trans (Nat.add_le_add card_image_le card_image_le)
  simpa only [card_product, card_sdiff_of_subset (subset_univ U), card_univ, U, core] using h

omit [Fintype I] [Nonempty I] in
/-- A second-order inclusion-exclusion lower bound on the union using uniform
individual sizes and pairwise overlap bounds. -/
private theorem union_lower {J : Type} [DecidableEq J] (S : Finset J) (C : J → Finset I)
    {w d : ℕ} (hw : ∀ i ∈ S, w ≤ (C i).card)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (C i ∩ C j).card ≤ d) :
    S.card*w ≤ (S.biUnion C).card + S.card.choose 2*d := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hsub : S ⊆ insert i S := subset_insert _ _
    have hrec := ih (fun j hj => hw j (hsub hj)) (fun x hx y hy => hd x (hsub hx) y (hsub hy))
    have hnew := hw i (mem_insert_self _ _)
    have hov : (C i ∩ S.biUnion C).card ≤ S.card*d := by
      have hcover : C i ∩ S.biUnion C ⊆ S.biUnion (fun j => C i ∩ C j) := by
        intro x hx
        obtain ⟨hx1,hx2⟩ := mem_inter.mp hx
        obtain ⟨j,hj,hxj⟩ := mem_biUnion.mp hx2
        exact mem_biUnion.mpr ⟨j,hj,mem_inter.mpr ⟨hx1,hxj⟩⟩
      apply ((card_le_card hcover).trans card_biUnion_le).trans
      exact (sum_le_sum (fun j hj => hd i (mem_insert_self _ _) j (hsub hj)
        (fun he => hi (he ▸ hj)))).trans_eq (by simp)
    have hc := card_union_add_card_inter (C i) (S.biUnion C)
    rw [card_insert_of_notMem hi, biUnion_insert, Nat.add_mul, one_mul,
      Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_mul]
    change S.card*w+w ≤ (C i ∪ S.biUnion C).card + (S.card*d+S.card.choose 2*d)
    omega

/-- The actual family of rich MCA witnesses stays within the three-head budget when
at most four large secants cover all but the allowed 16546 exceptional labels. The
geometric factor analysis is responsible for proving this coverage hypothesis. -/
theorem selected_card_of_few_heads (fam : BadScalarRichPointFamily dom k δ u)
    (G : Finset F) (hG : G ⊆ fam.G)
    (hn : Fintype.card I = 1073741824) (hk : k = 67108864) {e : ℕ}
    (hl : 671088640 ≤ e) (hu : e ≤ 715827881)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 1073741824-e)
    (H : Finset (LineParameter F)) (hH : H ⊆ lineParameters fam)
    (hfour : H.card ≤ 4) (hbig : ∀ c ∈ H, 512 < (pointsOn fam c).card)
    (hexception : (G \ H.biUnion (pointsOn fam)).card ≤ 16546) :
    G.card ≤ 3*(e+1) := by
  classical
  let D (c : LineParameter F) := jointCore dom (u 0) (u 1) c.1 c.2
  let U := H.biUnion D
  let B := H.biUnion (pointsOn fam)
  have hsub : G ⊆ (G \ B) ∪ B := by
    intro z hz
    by_cases hb : z ∈ B
    · exact mem_union_right _ hb
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hz,hb⟩)
  have htot := (card_le_card hsub).trans (card_union_le _ _)
  change (G \ B).card ≤ 16546 at hexception
  have hline (c : LineParameter F) (hc : c ∈ H) : (pointsOn fam c).card ≤ e+1 :=
    ArkLib.ProximityGap.Frontier.TwoLargeCoreCount.line_occupancy_le fam (by omega) ht (hH hc)
  by_cases hfew : H.card ≤ 2
  · have hB : B.card ≤ H.card*(e+1) :=
      card_biUnion_le.trans ((sum_le_sum (fun c hc => hline c hc)).trans_eq (by simp))
    have hb2 := Nat.mul_le_mul_right (e+1) hfew
    omega
  have hcore (c : LineParameter F) (hc : c ∈ H) : 356515842 ≤ (D c).card := by
    have hp := pointsOn_card_mul_max_add_core_le fam (hH hc)
    rw [ht, hn] at hp
    change (pointsOn fam c).card * max 1 (1073741824-e-(D c).card) + (D c).card ≤ _ at hp
    have hm : 513*(1073741824-e-(D c).card) ≤ (pointsOn fam c).card*
        max 1 (1073741824-e-(D c).card) :=
      Nat.mul_le_mul (hbig c hc) (Nat.le_max_right ..)
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < H.card by omega)
  by_cases hdet : ∀ c ∈ H, lineDeterminant a b c = 0
  · have hcount := collinear_card fam H hH a b hab hdet
    change B.card ≤ U.card+(Fintype.card I-U.card)*H.card at hcount
    rw [hn] at hcount
    have hpair (i : LineParameter F) (hi : i ∈ H) (j : LineParameter F) (hj : j ∈ H)
        (hij : i ≠ j) : (D i ∩ D j).card ≤ 67108863 := by
      have hi' := lineParameter_degree_lt fam (hH hi)
      have hj' := lineParameter_degree_lt fam (hH hj)
      have hne : i.1 ≠ j.1 ∨ i.2 ≠ j.2 := by
        by_contra! h
        exact hij (Prod.ext h.1 h.2)
      rw [hk] at hi' hj'
      exact ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.jointCore_inter_jointCore_card_le
        dom (u 0) (u 1) (by decide : 1 ≤ 67108864) hi'.1 hi'.2 hj'.1 hj'.2 hne
    have hU := union_lower H D hcore hpair
    change _ ≤ U.card + _ at hU
    have hUn := card_le_univ U
    rw [hn] at hUn
    rcases (show H.card = 3 ∨ H.card = 4 by omega) with hj | hj <;>
      rw [hj] at hcount hU <;> norm_num [Nat.choose] at hU <;> omega
  · push Not at hdet
    obtain ⟨c, hc, hnon⟩ := hdet
    have hnon' : ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantMultiplicity.threeLineDeterminant
        a b c ≠ 0 := by
      simpa only [ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantMultiplicity.threeLineDeterminant,
        lineDeterminant, mul_comm] using hnon
    have hcover := ArkLib.ProximityGap.Frontier.ThreeHeadDeterminantCover.cover_of_three_noncollinear
      fam (show 1 ≤ k by omega) a b c (hH ha) (hH hb) (hH hc) hnon' (by
        have h1 := hcore a ha
        have h2 := hcore b hb
        have h3 := hcore c hc
        rw [ht,hn]
        change _ < _ + (D a).card + (D b).card + (D c).card
        omega)
    have hg := (card_le_card (hG.trans hcover)).trans (card_union_le _ _)
    have hu' := card_union_le (pointsOn fam a) (pointsOn fam b)
    have h1 := hline a ha
    have h2 := hline b hb
    have h3 := hline c hc
    omega

section SecondPrime

open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open ArkLib.ProximityGap.Frontier
open scoped ENNReal

private abbrev prime := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
private abbrev generator := ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
local instance : Fact prime.Prime := ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- The named evaluation domain at the terminal rate-sixteenth predecessor. -/
noncomputable abbrev secondDomain := KKH26RegimeSplit.powDomain generator
  ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g
  (KKH26RegimeSplit.ne_zero_of_orderOf_eq ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g)

/-- The remaining geometric coverage statement, on an exact over-budget sample of
literal witnesses. It asks for the secants supplied by the interpolation factors. -/
def SecondPrimeHeadCover : Prop :=
  ∀ u : WordStack (ZMod prime) (Fin 2) (Fin (2^30)),
    let fam := canonicalBadScalarRichPointFamily secondDomain (k := 2^26)
      ((715827881 : ℝ≥0)/1073741824) u (by decide)
    ∀ G : Finset (ZMod prime), G ⊆ fam.G → G.card = 2147483649 →
      ∃ H : Finset (LineParameter (ZMod prime)), H ⊆ lineParameters fam ∧
        H.card ≤ 4 ∧ (∀ c ∈ H, 512 < (pointsOn fam c).card) ∧
        (G \ H.biUnion (pointsOn fam)).card ≤ 16546

/-- The geometric head-cover statement alone suffices for the exact named operational
threshold. The matching bad side is the kernel-checked three-core attack. -/
theorem secondPrime_threshold_of_head_cover (hcover : SecondPrimeHeadCover) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod prime)
      (evalCode generator (2^30) (2^26-1)) (epsStar : ℝ≥0∞) =
        (715827882 : ℝ≥0)/1073741824 := by
  apply le_antisymm (ThreeCoreSecondPrimeBracket.secondPrime_ceiling (by decide) (by decide))
  let N := TwoCorePackingThreshold.domainLength
  let e : ℕ := 715827881
  let δ : ℝ≥0 := (e : ℝ≥0)/(N : ℝ≥0)
  change ((e+1 : ℕ) : ℝ≥0)/(N : ℝ≥0) ≤ _
  rw [epsStar_coe_eq_natCast_inv]
  apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good (by decide) (by decide)
  simp only [predecessorRadius, Nat.add_sub_cancel]
  rw [KKH26RegimeSplit.evalCode_eq_reedSolomon generator
    ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g
    (KKH26RegimeSplit.ne_zero_of_orderOf_eq ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g)
    (2^26-1), show (2^26-1+1 : ℕ) = 2^26 by decide]
  apply le_trans _ (natCast_div_le_inv_of_mul_le (E := 2147483648) (by decide)
    ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P.pos (by decide))
  apply (epsMCA_le_of_badCount_le _ _ 2147483648 ?_).trans (by rw [ZMod.card])
  intro u
  let fam := canonicalBadScalarRichPointFamily secondDomain (k := 2^26) δ u (by decide)
  change fam.G.card ≤ 2147483648
  by_contra! hmore
  obtain ⟨G, hG, hcard⟩ := exists_subset_card_eq (show 2147483649 ≤ fam.G.card by omega)
  obtain ⟨H, hH, hfour, hbig, hex⟩ := hcover u G hG hcard
  have hb := selected_card_of_few_heads fam G hG (Fintype.card_fin _) (by decide)
    (e := e) (by decide) (by decide) (by
      exact TwoCorePackingThreshold.agreement_ceiling e (by decide)) H hH hfour hbig hex
  change G.card ≤ 3*(715827881+1) at hb
  omega

end SecondPrime

#print axioms collinear_card
#print axioms selected_card_of_few_heads
#print axioms secondPrime_threshold_of_head_cover

end ProximityGap.TerminalCollinearHeadCount
