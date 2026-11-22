/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.MaximalSecantCore

/-! # Characterizing the extra label by complementary cores at dimension three -/

namespace ProximityGap.DimensionThreeBalancedCores
open Finset Polynomial Code ArkLib.ProximityGap.Frontier
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines HalfPredecessorLargeCoreCollapse
open scoped NNReal ENNReal

/-- An overrun at the dimension-three odd predecessor forces two complementary
equal-sized secant cores. All labels off the first line agree on the entire
second core, and each line accounts for precisely half the labels. -/
theorem balanced {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F] {D : I ↪ F} {h : ℕ}
    {δ : ℝ≥0} {u : WordStack F (Fin 2) I} (fam : BadScalarRichPointFamily D 3 δ u)
    (large : 3≤h) (hn : Fintype.card I=2*h+2) (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=h+3)
    (exceeds : h<fam.G.card) :
    ∃ l∈lineParameters fam, ∃ l'∈lineParameters fam,
      let C := jointCore D (u 0) (u 1) l.1 l.2
      let V := jointCore D (u 0) (u 1) l'.1 l'.2
      C.card=h+1 ∧ V=Cᶜ ∧ 2*(pointsOn fam l).card=h+1 ∧ 2*(outsideLine fam l).card=h+1 ∧
        ∀ v∈outsideLine fam l, v∈pointsOn fam l' := by
  classical
  let core (l : LineParameter F) := jointCore D (u 0) (u 1) l.1 l.2
  let P (a : F) := fullAgreement D (u 0) (u 1) a (fam.q a)
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (by omega : 1<fam.G.card)
  obtain ⟨l,hl,best⟩ := exists_max_image (lineParameters fam) (fun l => (core l).card)
    ⟨_,secantParameter_mem_lineParameters fam ha hb hab⟩
  let C := core l
  let V := Cᶜ
  let A (x : F) := P x \ C
  let B (x : F) := P x ∩ C
  let O := outsideLine fam l
  let L := pointsOn fam l
  have sizeV : V.card=Fintype.card I-C.card := card_compl _
  have c_le := card_le_univ C
  have fresh {x : F} (hx : x∈O) : h+1≤(A x).card := by
    have b := threshold_sub_pred_le_fresh_card fam l (by decide) hl hx
    rw [ht] at b
    simpa only [A,P,C,core,show h+3-(3-1)=h+1 by omega] using b
  have subV (x : F) : A x ⊆ V := fun i hi => mem_compl.mpr (mem_sdiff.mp hi).2
  have part : L.card+O.card=fam.G.card := pointsOn_card_add_outsideLine_card fam l
  have cap : L.card≤h := by
    simpa only [show h-1+1=h by omega] using TwoLargeCoreCount.line_occupancy_le
      (e:=h-1) fam (by omega) ht hl
  obtain ⟨v,hv⟩ := card_pos.mp (by omega : 0<O.card)
  have cle : C.card≤h+1 := by
    have := (fresh hv).trans (card_le_card (subV v)); omega
  have pack := pointsOn_card_mul_max_add_core_le fam hl
  rw [ht,hn] at pack
  change L.card * max 1 (h+3-C.card)+C.card≤2*h+2 at pack
  rw [max_eq_right (by omega : 1≤h+3-C.card)] at pack
  have ltwo : 2≤L.card := two_le_pointsOn_card_of_mem_lineParameters fam hl
  have two : 2≤O.card := by
    have mul := Nat.mul_le_mul_left (L.card-1) (show 2≤h+3-C.card by omega)
    have split := Nat.succ_mul (L.card-1) (h+3-C.card)
    rw [show (L.card-1).succ=L.card by omega] at split
    omega
  have meet {x y : F} (hx : x∈O) (hy : y∈O) (xy : x≠y) :
      P x ∩ P y=core (secantParameter fam x y) := by
    let m := secantParameter fam x y
    have xx := first_point_mem_pointsOn_secant fam (beta:=y) ((mem_outsideLine_iff ..).mp hx).1
    have yy := second_point_mem_pointsOn_secant fam ((mem_outsideLine_iff ..).mp hy).1 xy
    change P x ∩ P y=core m
    dsimp only [P,core]
    rw [((mem_pointsOn_iff fam m x).mp xx).2,((mem_pointsOn_iff fam m y).mp yy).2]
    exact fullAgreement_inter_eq_jointCore D (u 0) (u 1) _ _ xy
  have overlaps {x y : F} (hx : x∈O) (hy : y∈O) (xy : x≠y) :
      (A x).card=h+1 ∧ A x ∩ A y=P x ∩ P y := by
    have capMeet : (P x ∩ P y).card≤C.card := by
      rw [meet hx hy xy]
      exact best _ (secantParameter_mem_lineParameters fam ((mem_outsideLine_iff ..).mp hx).1
        ((mem_outsideLine_iff ..).mp hy).1 xy)
    have sub : A x ∩ A y ⊆ P x ∩ P y := inter_subset_inter sdiff_subset sdiff_subset
    have hi := card_le_card sub
    have hu := card_le_card (union_subset (subV x) (subV y))
    have sum := card_union_add_card_inter (A x) (A y)
    have lowX := fresh hx
    have lowY := fresh hy
    exact ⟨by omega,eq_of_subset_of_card_le sub (by omega)⟩
  have dem (x : F) (hx : x∈O) : (A x).card=h+1 ∧ 2≤(B x).card := by
    obtain ⟨i,hi,j,hj,ij⟩ := one_lt_card.mp two
    have ha : (A x).card=h+1 := by
      by_cases xi : x=i
      · exact (overlaps hx hj (xi ▸ ij)).1
      · exact (overlaps hx hi xi).1
    have b := fam.threshold_le x ((mem_outsideLine_iff ..).mp hx).1
    rw [ht] at b
    change h+3≤(P x).card at b
    have sums : (A x).card+(B x).card=(P x).card := card_sdiff_add_card_inter _ _
    exact ⟨ha,by omega⟩
  have dis : (O : Set F).PairwiseDisjoint B := by
    intro x hx y hy xy
    apply disjoint_left.mpr
    intro i hix hiy
    have hi : i∈P x ∩ P y := mem_inter.mpr ⟨(mem_inter.mp hix).1,(mem_inter.mp hiy).1⟩
    rw [←(overlaps hx hy xy).2] at hi
    exact (mem_sdiff.mp (mem_inter.mp hi).1).2 (mem_inter.mp hix).2
  have inside : O.card*2≤C.card := by
    calc
      _ = ∑ _x ∈ O, 2 := by simp
      _ ≤ ∑ x ∈ O, (B x).card := sum_le_sum fun x hx => (dem x hx).2
      _ = _ := (card_biUnion dis).symm
      _ ≤ _ := card_le_card (biUnion_subset.mpr fun _ _ => inter_subset_right)
  have left : L.card*2+C.card≤2*h+2 :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left L.card (by omega : 2≤h+3-C.card)) _).trans pack
  have eqc : C.card=h+1 := by
    by_contra! smaller
    have mul := Nat.mul_le_mul_left L.card (by omega : 3≤h+3-C.card)
    omega
  have onV (x : F) (hx : x∈O) : A x=V :=
    eq_of_subset_of_card_le (subV x) (by have := (dem x hx).1;omega)
  obtain ⟨x,hx,y,hy,xy⟩ := one_lt_card.mp two
  let l' := secantParameter fam x y
  have hl' := secantParameter_mem_lineParameters fam ((mem_outsideLine_iff ..).mp hx).1
    ((mem_outsideLine_iff ..).mp hy).1 xy
  have eqv : core l'=V := by
    rw [←meet hx hy xy,←(overlaps hx hy xy).2,onV x hx,onV y hy,inter_self]
  refine ⟨l,hl,l',hl',eqc,eqv,(by omega : 2*L.card=h+1),(by omega : 2*O.card=h+1),?_⟩
  intro z hz
  by_contra off
  have hzo := (mem_outsideLine_iff fam l' z).mpr
    ⟨((mem_outsideLine_iff fam l z).mp hz).1,fun he => off ((mem_pointsOn_iff fam l' z).mpr
      ⟨((mem_outsideLine_iff fam l z).mp hz).1,he⟩)⟩
  have bound := threshold_sub_pred_le_fresh_card fam l' (by decide) hl' hzo
  rw [ht] at bound
  change h+3-(3-1)≤(P z \ core l').card at bound
  rw [eqv] at bound
  have sv : V⊆P z := onV z hz ▸ (sdiff_subset : A z⊆P z)
  have small := fullAgreement_inter_jointCore_card_le D (u 0) (u 1) (by decide : 1≤3)
    (fam.degree_lt z ((mem_outsideLine_iff fam l' z).mp hzo).1)
    (lineParameter_degree_lt fam hl').1 (lineParameter_degree_lt fam hl').2
    ((mem_outsideLine_iff fam l' z).mp hzo).2
  change (P z ∩ core l').card≤3-1 at small
  rw [eqv,inter_eq_right.mpr sv] at small
  omega

end ProximityGap.DimensionThreeBalancedCores
#print axioms ProximityGap.DimensionThreeBalancedCores.balanced
