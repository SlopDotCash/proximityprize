/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorPuncturedList
import ArkLib.Research.ProximityGap.Frontier.PuncturedFourWordLabels
import ArkLib.Research.ProximityGap.Frontier.ApolarHalfBreakpoint

/-! # The first named half-rate successor is equivalent to a punctured four-word list -/

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open Polynomial Finset Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.HalfSuccessorListEquivalence
open _root_.ProximityGap
open _root_.ProximityGap.FourHeadWitness
open HalfPredecessorBadEventRichPointBridge
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]
private abbrev n : ℕ := 1073741824
private abbrev t : ℕ := 805306366
private abbrev δ₁ : ℝ≥0 := 268435457/1073741824

/-- Four distinct lower-dimension messages within 268435457 errors of a common word
on the complement of a single coordinate. -/
def HasPuncturedList (dom : I ↪ F) : Prop :=
  ∃ (a : I) (q : Fin 4 → F[X]) (w : I → F), Function.Injective q ∧
    (∀ i, (q i).natDegree ≤ 536870910) ∧
    ∀ i, t ≤ (univ.filter fun x => x ≠ a ∧ (q i).eval (dom x) = w x).card

/-- Any such punctured list yields a received row pair with at least two more
actual bad scalar labels than the block length. -/
theorem n_plus_two (dom : I ↪ F) (hn : Fintype.card I = n)
    (hF : 1073741827^2 < Fintype.card F) (hlist : HasPuncturedList dom) :
    ∃ u : WordStack F (Fin 2) I, 1073741826 ≤ (badScalars dom 536870912 δ₁ u).card := by
  classical
  obtain ⟨a,q,w,hinj,hq,hw⟩ := hlist
  let B := (univ : Finset I).erase a
  let incl : B ↪ I := ⟨Subtype.val,Subtype.val_injective⟩
  let D := incl.trans dom
  let Cores (i : Fin 4) := univ.filter fun x => x ≠ a ∧ (q i).eval (dom x) = w x
  let E (i : Fin 4) := univ.filter fun x : B => (q i).eval (D x) ≠ w x.val
  let V := univ.image fun i => (q i).eval (dom a)
  let O := (univ.biUnion E).map incl
  have hBn : Fintype.card B+1 = 4*268435456 := by
    rw [Fintype.card_coe,show B=univ.erase a from rfl,card_erase_of_mem (mem_univ _),card_univ,hn]
    decide
  have hmiss (i : Fin 4) : (E i).card ≤ 268435457 := by
    let A := univ.filter (fun x : B => (q i).eval (D x) = w x.val)
    have hm : A.map incl = Cores i := by
      ext x
      constructor
      · intro hx
        obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
        exact mem_filter.mpr ⟨mem_univ _,(mem_erase.mp y.property).1,(mem_filter.mp hy).2⟩
      · intro hx
        obtain ⟨_,hxa,hxq⟩ := mem_filter.mp hx
        let y : B := ⟨x,mem_erase.mpr ⟨hxa,mem_univ _⟩⟩
        exact mem_map.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,hxq⟩,rfl⟩
    have hcard : A.card = (Cores i).card := (card_map _).symm.trans (congrArg card hm)
    have he := (univ : Finset B).card_filter_add_card_filter_not (fun x => (q i).eval (D x) = w x.val)
    change A.card+(E i).card = _ at he
    rw [card_univ] at he
    have hc : 805306366 ≤ (Cores i).card := hw i
    omega
  have hlabels := _root_.ProximityGap.PuncturedFourWordLabels.count D q (fun x => w x.val) (dom a)
    (by rintro ⟨x,hx⟩; exact (mem_erase.mp x.property).1 (dom.injective hx))
    268435456 hBn hinj (fun i => by have := hq i; omega) hmiss
  change 1073741826 ≤ (univ.biUnion E).card+V.card at hlabels
  have hO : O.card = (univ.biUnion E).card := card_map _
  have hOsmall : O.card ≤ 1073741823 := by
    have h := card_le_univ (univ.biUnion E)
    omega
  have hV : V.card ≤ 4 := card_image_le.trans (by simp)
  have ht : ⌈(1-δ₁)*(Fintype.card I : ℝ≥0)⌉₊ = 805306367 := by
    rw [hn]
    have h := TwoCorePackingThreshold.agreement_ceiling 268435457 (by decide)
    rw [Fintype.card_fin] at h
    exact h
  let alloc : CoreAllocation dom 536870912 δ₁ := {
    head := q, background := w, ordinary := O, special := {a}, core := Cores
    degree_head := fun i => (degree_le_natDegree (p:=q i)).trans_lt (WithBot.coe_lt_coe.mpr ((hq i).trans_lt (by decide)))
    degree_first := fun i => (degree_le_natDegree (p:=Polynomial.X * q i)).trans_lt (WithBot.coe_lt_coe.mpr ((natDegree_mul_le (p:=Polynomial.X) (q:=q i)).trans_lt
      (by rw [natDegree_X]; have := hq i; omega)))
    disjoint := disjoint_left.mpr (by
      intro x hx ha
      obtain ⟨y,_,rfl⟩ := mem_map.mp hx
      exact (mem_erase.mp y.property).1 (mem_singleton.mp ha))
    core_disjoint := fun i => disjoint_left.mpr (by
      intro x hx ha
      exact (mem_filter.mp hx).2.1 (mem_singleton.mp ha))
    core_agrees := fun i x hx => (mem_filter.mp hx).2.2
    core_rank := fun i => (show 536870912 ≤ t by decide).trans (hw i)
    core_size := fun i => Nat.ceil_le.mp (by rw [ht]; have hc : t ≤ (Cores i).card := hw i; unfold t at hc; omega)
    ordinary_mismatch := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hy
      exact ⟨i,(mem_filter.mp hi).2⟩ }
  have hcount : alloc.count = O.card+V.card := by
    simp [alloc,CoreAllocation.count,V]
  obtain ⟨u,G,hG,hbad⟩ := exists_bad_scalar_set_of_values alloc (by omega) (by
    rw [hcount]
    have hsum : O.card+V.card ≤ 1073741827 := by omega
    exact (Nat.mul_le_mul hsum hsum).trans_lt (by simpa only [pow_two] using hF))
  have hinc : G ⊆ badScalars dom 536870912 δ₁ u := fun z hz => (mem_badScalars_iff ..).mpr (hbad z hz)
  have hle := card_le_card hinc
  rw [hG,hcount,hO] at hle
  exact ⟨u,hlabels.trans hle⟩

open ArkLib.ProximityGap.KKH26 (evalCode)
open PrizeShapeRateHalfBracket
private abbrev p := PrizeShapePrimeP30.P
private abbrev g := PrizeShapePrimeP30.g
local instance : Fact p.Prime := ⟨PrizeShapePrimeP30.prime_P⟩

/-- The actual first-prime failure at this Hamming step, at every positive width,
is equivalent to existence of the punctured four-word list. -/
theorem first_prime_iff (width : ℕ) [NeZero width] :
    ((epsStar : ℝ≥0∞) < epsMCA (F:=ZMod p)
      ((evalCode g (2^30) (2^29-1) : Set (Fin (2^30) → ZMod p)) ^⋈ (Fin width)) δ₁) ↔
      HasPuncturedList firstDomain := by
  rw [KKH26RegimeSplit.evalCode_eq_reedSolomon g PrizeShapePrimeP30.orderOf_g
    (KKH26RegimeSplit.ne_zero_of_orderOf_eq PrizeShapePrimeP30.orderOf_g) (2^29-1)]
  rw [epsMCA_interleaved_eq]
  constructor
  · intro hbad
    apply HalfSuccessorPuncturedList.first_prime
    rwa [KKH26RegimeSplit.evalCode_eq_reedSolomon g PrizeShapePrimeP30.orderOf_g
      (KKH26RegimeSplit.ne_zero_of_orderOf_eq PrizeShapePrimeP30.orderOf_g) (2^29-1)]
  · intro hlist
    obtain ⟨u,hu⟩ := n_plus_two firstDomain (Fintype.card_fin _) (by rw [ZMod.card]; decide) hlist
    let G := badScalars firstDomain 536870912 δ₁ u
    have hmass := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
      (ReedSolomon.code firstDomain 536870912 : Set (Fin (2^30) → ZMod p)) δ₁ u G
      (fun z hz => (mem_badScalars_iff ..).mp hz)
    apply lt_of_lt_of_le _ hmass
    rw [ZMod.card,epsStar_coe_eq_natCast_inv]
    apply SeventeenThirtyTwoDeltaStarFloor.inv_natCast_lt_natCast_div (by decide) PrizeShapePrimeP30.prime_P.pos
    exact (show p < 2^128*1073741826 by decide).trans_le (Nat.mul_le_mul_left _ hu)

open _root_.ProximityGap.MCAThresholdLedger

/-- Existence of the punctured list is equivalent to exact equality of the original
first-prime operational supremum with the first half-rate successor. -/
theorem first_prime_supremum_iff (width : ℕ) [NeZero width] :
    mcaDeltaStar (F:=ZMod p) ((RateHalfApolarThreshold.code g) ^⋈ (Fin width)) (epsStar : ℝ≥0∞) = δ₁
      ↔ HasPuncturedList firstDomain := by
  have hc : RateHalfApolarThreshold.code g =
      (ReedSolomon.code firstDomain 536870912 : Set (Fin (2^30) → ZMod p)) :=
    KKH26RegimeSplit.evalCode_eq_reedSolomon g PrizeShapePrimeP30.orderOf_g
      (KKH26RegimeSplit.ne_zero_of_orderOf_eq PrizeShapePrimeP30.orderOf_g) (2^29-1)
  have he := first_prime_iff 1
  change ((epsStar : ℝ≥0∞) < epsMCA (F:=ZMod p) ((RateHalfApolarThreshold.code g) ^⋈ (Fin 1)) δ₁) ↔ _ at he
  rw [hc,epsMCA_interleaved_eq,← hc] at he
  rw [hc,mcaDeltaStar_interleaved_eq,← hc]
  constructor
  · intro hval
    apply he.mp
    by_contra! good
    have hl := latticeBoundary_le_mcaDeltaStar_of_predecessor_good (n:=n) (a:=268435458)
      (by decide) (by decide) (RateHalfApolarThreshold.code g) (epsStar : ℝ≥0∞) good
    rw [hval] at hl
    have hlt : δ₁ < (268435458:ℝ≥0)/n :=
      (div_lt_div_iff_of_pos_right (by norm_num [n] : (0:ℝ≥0) < n)).mpr (by norm_num [δ₁])
    exact hl.not_gt hlt
  · intro hlist
    exact le_antisymm (mcaDeltaStar_le_of_bad _ _ (he.mpr hlist)) ApolarHalfBreakpoint.named_prime_floors.1

#print axioms first_prime_supremum_iff
#print axioms n_plus_two
#print axioms first_prime_iff
end ArkLib.ProximityGap.Frontier.HalfSuccessorListEquivalence
