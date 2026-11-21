/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorFourHeadCover
import ArkLib.Research.ProximityGap.Frontier.FourHeadWitness

/-! # A literal punctured four-word list from an over-budget half-rate MCA family -/

set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.HalfSuccessorPuncturedList
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry HalfPredecessorSecantLines
open HalfPredecessorRateQuarterDeterminantMultiplicity HalfPredecessorRateQuarterDeterminantCollapse
open HalfPredecessorRateQuarterPrimitiveDirection
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- On every injective production-size domain, an over-budget actual family at 268435457
errors yields one puncture, four distinct lower-dimension polynomials and a single received
word with 805306366 agreements per polynomial away from the puncture. -/
theorem extraction {p : ℕ} [CharP F p] (hp : 116 < p) (fam : BadScalarRichPointFamily dom 536870912 δ u)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 805306367)
    (hbig : 1073741824 < fam.G.card) :
    ∃ (a : I) (q : Fin 4 → F[X]) (w : I → F), Function.Injective q ∧
      (∀ i, (q i).natDegree ≤ 536870910) ∧
      ∀ i, 805306366 ≤ (univ.filter fun x => x ≠ a ∧ (q i).eval (dom x) = w x).card := by
  classical
  obtain ⟨H,hH,hfour,hall,hlarge⟩ := HalfSuccessorFourHeadCover.cover hp fam hn ht hbig
  let Cores (l : LineParameter F) := jointCore dom (u 0) (u 1) l.1 l.2
  let U := H.biUnion Cores
  have hcore (l) (hl : l∈H) : 805306366 ≤ (Cores l).card := by
    have h := pointsOn_card_mul_max_add_core_le fam (hH hl)
    rw [ht,hn] at h
    change (pointsOn fam l).card * max 1 (805306367-(Cores l).card)+(Cores l).card ≤ _ at h
    have hmul := Nat.mul_le_mul (hlarge l hl) (Nat.le_max_right 1 (805306367-(Cores l).card))
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (show 1 < H.card by omega)
  have hdeg (l) (hl : l∈H) := lineParameter_degree_lt fam (hH hl)
  have hdet (l) (hl : l∈H) : lineDeterminant a b l = 0 := by
    by_contra hd
    have hd' : threeLineDeterminant a b l ≠ 0 := by
      simpa only [threeLineDeterminant,lineDeterminant,mul_comm] using hd
    have h := ThreeHeadDeterminantCover.core_sum_le_union_add_degree dom (u 0) (u 1) a b l hd'
    simp only [coreSet_eq_jointCore] at h
    change (Cores a).card+(Cores b).card+(Cores l).card ≤
      (Cores a ∪ Cores b ∪ Cores l).card+(threeLineDeterminant a b l).natDegree at h
    have hD := natDegree_threeLineDeterminant_le_two_mul_sub_two (hdeg a ha).1 (hdeg a ha).2
      (hdeg b hb).1 (hdeg b hb).2 (hdeg l hl).1 (hdeg l hl).2
    have hU := card_le_univ (Cores a ∪ Cores b ∪ Cores l)
    have h1 := hcore a ha
    have h2 := hcore b hb
    have h3 := hcore l hl
    omega
  let S := primitiveIntercept a b
  let T := primitiveSlope a b
  have hbound := _root_.ProximityGap.TerminalCollinearHeadCount.collinear_card_image fam H hH a b hab hdet
  change (H.biUnion (pointsOn fam)).card ≤ (U.image (fun i => primitiveScalarAt a b (dom i))).card +
    (Fintype.card I-U.card)*H.card at hbound
  rw [hfour,hn] at hbound
  have hUbound := card_le_univ U
  have hpop := card_le_card hall
  have him := card_image_le (s:=U) (f:=fun i => primitiveScalarAt a b (dom i))
  have hUne : U ≠ univ := by
    intro h
    have hcard : U.card = Fintype.card I := by rw [h,card_univ]
    omega
  obtain ⟨hole,hh⟩ := not_forall.mp (show ¬ ∀ x, x∈U from fun he => hUne (eq_univ_iff_forall.mpr he))
  have hjoint : (Cores a ∩ Cores b).card ≤ 536870911 :=
    FSMBCoreAbsorptionLadder.jointCore_inter_jointCore_card_le dom (u 0) (u 1) (by decide : 1 ≤ 536870912)
      (hdeg a ha).1 (hdeg a ha).2 (hdeg b hb).1 (hdeg b hb).2
      (by by_contra! he; exact hab (Prod.ext he.1 he.2))
  have incl (l) (hl : l∈H) : Cores l ⊆ U := subset_biUnion_of_mem Cores hl
  have hu := card_le_card (union_subset (incl a ha) (incl b hb))
  have hc := card_union_add_card_inter (Cores a) (Cores b)
  have ha' := hcore a ha
  have hb' := hcore b hb
  have hdir : 0 < S.natDegree ∨ 0 < T.natDegree := by
    by_contra! h0
    have he (x : I) : primitiveScalarAt a b (dom x) = -((S.coeff 0)/(T.coeff 0)) := by
      change -(S.eval _ / T.eval _) = _
      rw [eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h0.1),
        eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h0.2)]
      simp
    have hsmall : (U.image (fun i => primitiveScalarAt a b (dom i))).card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := mem_image.mp hy
      exact (he i).trans (he j).symm
    omega
  let e : Fin 4 ≃ H := Fintype.equivOfCardEq (by simpa using hfour.symm)
  have hrep (i : Fin 4) := exists_polynomial_factor_of_lineDeterminant_eq_zero a b (e i).val
    hab (hdet _ (e i).property)
  choose D hA hB using hrep
  have hinj : Function.Injective D := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    apply Prod.ext
    · exact sub_left_injective ((hA i).trans ((congrArg (_ * ·) hij).trans (hA j).symm))
    · exact sub_left_injective ((hB i).trans ((congrArg (_ * ·) hij).trans (hB j).symm))
  have hDegree (i : Fin 4) : (D i).natDegree ≤ 536870910 := by
    by_cases hz : D i = 0
    · simp [hz]
    rcases hdir with hs | ht'
    · have hS : S ≠ 0 := fun h => by simp [h] at hs
      have hbound := (natDegree_sub_le (e i).val.1 a.1).trans_lt (max_lt (hdeg _ (e i).property).1 (hdeg a ha).1)
      rw [hA i,natDegree_mul hS hz] at hbound
      omega
    · have hT : T ≠ 0 := fun h => by simp [h] at ht'
      have hbound := (natDegree_sub_le (e i).val.2 a.2).trans_lt (max_lt (hdeg _ (e i).property).2 (hdeg a ha).2)
      rw [hB i,natDegree_mul hT hz] at hbound
      omega
  obtain ⟨A,B,hAB⟩ := primitiveDirection_isCoprime hab
  let w (x : I) := A.eval (dom x)*(u 0 x-a.1.eval (dom x))+B.eval (dom x)*(u 1 x-a.2.eval (dom x))
  refine ⟨hole,D,w,hinj,hDegree,fun i => (hcore _ (e i).property).trans (card_le_card ?_)⟩
  intro x hx
  have hag := (mem_filter.mp hx).2
  have hax := congrArg (fun p : F[X] => p.eval (dom x)) (hA i)
  have hbx := congrArg (fun p : F[X] => p.eval (dom x)) (hB i)
  have hux := congrArg (fun p : F[X] => p.eval (dom x)) hAB
  simp only [eval_sub,eval_add,eval_mul,eval_one] at hax hbx hux
  apply mem_filter.mpr
  refine ⟨mem_univ _,fun he => hh (he ▸ incl _ (e i).property hx),?_⟩
  dsimp [w]
  rw [← hag.1,← hag.2,hax,hbx]
  linear_combination -(D i).eval (dom x)*hux

section FirstPrime
open _root_.ProximityGap
open _root_.ProximityGap.FourHeadWitness (firstDomain)
open ArkLib.ProximityGap.KKH26 (evalCode)
open PrizeShapeRateHalfBracket
open scoped ENNReal

private abbrev p := PrizeShapePrimeP30.P
private abbrev g := PrizeShapePrimeP30.g
private abbrev n := 2^30
private abbrev δ₁ : ℝ≥0 := 268435457/1073741824
local instance : Fact p.Prime := ⟨PrizeShapePrimeP30.prime_P⟩

/-- If the sponsor's actual first-prime probability budget fails at the first
half-rate successor, one punctured domain admits four distinct degree-at-most-536870910
messages within 268435457 errors of a common received word. -/
theorem first_prime
    (hbad : (epsStar : ℝ≥0∞) < epsMCA (F:=ZMod p) (evalCode g n (2^29-1)) δ₁) :
    ∃ (a : Fin n) (q : Fin 4 → (ZMod p)[X]) (w : Fin n → ZMod p), Function.Injective q ∧
      (∀ i, (q i).natDegree ≤ 536870910) ∧
      ∀ i, 805306366 ≤ (univ.filter fun x => x ≠ a ∧ (q i).eval (firstDomain x) = w x).card := by
  classical
  change (epsStar : ℝ≥0∞) < epsMCA (F:=ZMod p) (evalCode g (2^30) (2^29-1)) δ₁ at hbad
  rw [KKH26RegimeSplit.evalCode_eq_reedSolomon g PrizeShapePrimeP30.orderOf_g
    (KKH26RegimeSplit.ne_zero_of_orderOf_eq PrizeShapePrimeP30.orderOf_g) (2^29-1)] at hbad
  let code := (ReedSolomon.code firstDomain 536870912 : Set (Fin n → ZMod p))
  change (epsStar : ℝ≥0∞) < epsMCA (F:=ZMod p) code δ₁ at hbad
  have hex : ∃ u : Code.WordStack (ZMod p) (Fin 2) (Fin n), n < (badScalars firstDomain 536870912 δ₁ u).card := by
    by_contra! h
    have hc := epsMCA_le_of_badCount_le (F:=ZMod p) code δ₁ n h
    rw [ZMod.card] at hc
    apply hbad.not_ge (hc.trans ?_)
    rw [epsStar_coe_eq_natCast_inv]
    exact natCast_div_le_inv_of_mul_le (Q:=2^128) (by decide) PrizeShapePrimeP30.prime_P.pos (by decide)
  obtain ⟨u,hu⟩ := hex
  exact extraction (p:=p) (by decide) (canonicalBadScalarRichPointFamily firstDomain δ₁ u (by decide))
    (Fintype.card_fin _) (TwoCorePackingThreshold.agreement_ceiling 268435457 (by decide)) hu

end FirstPrime

#print axioms first_prime
#print axioms extraction
end ArkLib.ProximityGap.Frontier.HalfSuccessorPuncturedList
