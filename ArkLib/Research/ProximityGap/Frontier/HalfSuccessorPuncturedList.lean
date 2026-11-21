/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorFourHeadCover
import ArkLib.Research.ProximityGap.Frontier.FourHeadWitness
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA

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

/-- For four large sets with bounded pairwise intersections, the two-set union
lower bound is strict when their four complements cannot be disjoint in that union. -/
theorem four_core_union {J : Type*} [DecidableEq J] (U : Finset J) (V : Fin 4 → Finset J)
    {w d : ℕ} (hU : ∀ i, V i ⊆ U) (hw : ∀ i, w ≤ (V i).card)
    (hd : ∀ i j, i ≠ j → (V i ∩ V j).card ≤ d) (hgap : 3*d < 2*w) :
    2*w < U.card+d := by
  classical
  by_contra! hsmall
  have hpair (i j : Fin 4) (hne : i ≠ j) :
      V i ∪ V j = U ∧ (V i).card = w := by
    have h := card_union_add_card_inter (V i) (V j)
    have hsub := union_subset (hU i) (hU j)
    have hc := card_le_card hsub
    have hI := hd i j hne
    have h1 := hw i
    have h2 := hw j
    exact ⟨eq_of_subset_of_card_le hsub (by omega),by omega⟩
  have hsize (i : Fin 4) : (V i).card = w := by
    by_cases hi : i = 0
    · subst i
      exact (hpair 0 1 (by decide)).2
    · exact (hpair i 0 hi).2
  let W (i : Fin 4) := U \ V i
  have hdisj : ((univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint W := by
    intro i _ j _ hne
    apply disjoint_left.mpr
    intro x hx hy
    have hxl := (mem_sdiff.mp hx)
    have hxr := (mem_sdiff.mp hy)
    rw [← (hpair i j hne).1] at hxl
    exact (mem_union.mp hxl.1).elim hxl.2 hxr.2
  have hinc : univ.biUnion W ⊆ U := by
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    exact (mem_sdiff.mp hi).1
  have hmon := card_le_card hinc
  rw [card_biUnion hdisj] at hmon
  have hW (i : Fin 4) : (W i).card = U.card-w := by
    change (U \ V i).card = _
    rw [card_sdiff_of_subset (hU i),hsize]
  simp only [hW,sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at hmon
  have hwu := (hw 0).trans (card_le_card (hU 0))
  have he := hpair 0 1 (by decide)
  have hsize' := card_union_add_card_inter (V 0) (V 1)
  rw [he.1,hsize,hsize] at hsize'
  have hp := hd 0 1 (by decide)
  omega

/-- On every injective production-size domain, an over-budget actual family at 268435457
errors yields one puncture, four distinct lower-dimension polynomials and a single received
word with 805306366 agreements per polynomial away from the puncture. -/
theorem cap_and_extraction {p : ℕ} [CharP F p] (hp : 116 < p) (fam : BadScalarRichPointFamily dom 536870912 δ u)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 805306367)
    (hbig : 1073741824 < fam.G.card) :
    fam.G.card ≤ 1073741827 ∧ ∃ (a : I) (q : Fin 4 → F[X]) (w : I → F), Function.Injective q ∧
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
  have hagree (i : Fin 4) (x : I) (hx : x∈Cores (e i).val) : (D i).eval (dom x) = w x := by
    have hag := (mem_filter.mp hx).2
    have hax := congrArg (fun p : F[X] => p.eval (dom x)) (hA i)
    have hbx := congrArg (fun p : F[X] => p.eval (dom x)) (hB i)
    have hux := congrArg (fun p : F[X] => p.eval (dom x)) hAB
    simp only [eval_sub,eval_add,eval_mul,eval_one] at hax hbx hux
    dsimp [w]
    rw [← hag.1,← hag.2,hax,hbx]
    linear_combination -(D i).eval (dom x)*hux
  have hinter (i j : Fin 4) (hne : i ≠ j) : (Cores (e i).val ∩ Cores (e j).val).card ≤ 536870910 := by
    by_contra! h
    apply hne
    apply hinj
    let common := Cores (e i).val ∩ Cores (e j).val
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (D i) (D j) (f:=fun x : common => dom x.val)
      (dom.injective.comp Subtype.val_injective)
    · intro x
      exact (hagree i x.val (mem_inter.mp x.property).1).trans (hagree j x.val (mem_inter.mp x.property).2).symm
    · rw [Fintype.card_coe]
      exact max_lt ((hDegree i).trans_lt h) ((hDegree j).trans_lt h)
  have hunion := four_core_union U (fun i => Cores (e i).val) (fun i => incl _ (e i).property)
    (fun i => hcore _ (e i).property) hinter (by decide)
  refine ⟨by omega,hole,D,w,hinj,hDegree,fun i => (hcore _ (e i).property).trans (card_le_card ?_)⟩
  intro x hx
  exact mem_filter.mpr ⟨mem_univ _,fun he => hh (he ▸ incl _ (e i).property hx),hagree i x hx⟩

/-- On every injective production-size domain, an over-budget actual family at 268435457
errors yields one puncture, four distinct lower-dimension polynomials and a single received
word with 805306366 agreements per polynomial away from the puncture. -/
theorem extraction {p : ℕ} [CharP F p] (hp : 116 < p) (fam : BadScalarRichPointFamily dom 536870912 δ u)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 805306367)
    (hbig : 1073741824 < fam.G.card) :
    ∃ (a : I) (q : Fin 4 → F[X]) (w : I → F), Function.Injective q ∧
      (∀ i, (q i).natDegree ≤ 536870910) ∧
      ∀ i, 805306366 ≤ (univ.filter fun x => x ≠ a ∧ (q i).eval (dom x) = w x).card := by
  exact (cap_and_extraction hp fam hn ht hbig).2

/-- Every actual family at the first half-rate successor has at most three labels
beyond the first named field's block-length budget. -/
theorem family_cap {p : ℕ} [CharP F p] (hp : 116 < p) (fam : BadScalarRichPointFamily dom 536870912 δ u)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 805306367) :
    fam.G.card ≤ 1073741827 := by
  by_cases h : 1073741824 < fam.G.card
  · exact (cap_and_extraction hp fam hn ht h).1
  · omega

open _root_.ProximityGap
open scoped ENNReal

/-- At every positive interleaving width the probability of the first-successor
MCA event is at most the block length plus three divided by the field cardinality. -/
theorem eps_cap {p : ℕ} [CharP F p] (hp : 116 < p) (dom : I ↪ F)
    (hn : Fintype.card I = 1073741824) (width : ℕ) [NeZero width] :
    epsMCA (F:=F) ((ReedSolomon.code dom 536870912 : Set (I → F)) ^⋈ (Fin width)) ((268435457:ℝ≥0)/1073741824) ≤
      (1073741827:ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  rw [epsMCA_interleaved_eq]
  apply epsMCA_le_of_badCount_le
  intro u
  let fam := canonicalBadScalarRichPointFamily dom (k:=536870912) ((268435457:ℝ≥0)/1073741824) u (by decide)
  apply family_cap hp fam hn
  rw [hn]
  have ht := TwoCorePackingThreshold.agreement_ceiling 268435457 (by decide)
  rw [Fintype.card_fin] at ht
  exact ht

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
#print axioms eps_cap
#print axioms family_cap
#print axioms extraction
end ArkLib.ProximityGap.Frontier.HalfSuccessorPuncturedList
