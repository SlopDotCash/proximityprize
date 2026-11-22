/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier._TwoLargeCoreCount
import ArkLib.Research.ProximityGap.Frontier.OddRedundancyApolar
import ArkLib.Research.ProximityGap.Frontier.UniversalTwoHeadBudget

/-! # A maximal secant core and the exact dimension-two odd predecessor -/

namespace ProximityGap.MaximalSecantCore
open Finset Polynomial Code ArkLib.ProximityGap.Frontier MCAThresholdLedger
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines HalfPredecessorLargeCoreCollapse
open scoped NNReal ENNReal

/-- When twice the minimum number of fresh agreements of an outside point
exceeds the length, the secant with the largest core leaves at most one
outside point. If it has one, the other points each need at least two
fresh agreements on the line. -/
theorem family_bound {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F] {D : I ↪ F} {k e t : ℕ}
    {δ : ℝ≥0} {u : WordStack F (Fin 2) I} (fam : BadScalarRichPointFamily D k δ u)
    (hk : 2≤k) (hn : Fintype.card I=e+t) (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=t)
    (room : 2*(e+k-1)<Fintype.card I) : fam.G.card≤e+1 := by
  classical
  by_contra! exceeds
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (by omega : 1<fam.G.card)
  let C (l : LineParameter F) := jointCore D (u 0) (u 1) l.1 l.2
  let P (a : F) := fullAgreement D (u 0) (u 1) a (fam.q a)
  obtain ⟨l,hl,best⟩ := exists_max_image (lineParameters fam) (fun l => (C l).card)
    ⟨_,secantParameter_mem_lineParameters fam ha hb hab⟩
  let V := (C l)ᶜ
  have sizeV : V.card=Fintype.card I-(C l).card := card_compl _
  have fresh {a : F} (h : a∈outsideLine fam l) : t-(k-1)≤(P a \ C l).card := by
    simpa only [ht,P,C] using threshold_sub_pred_le_fresh_card fam l (by omega) hl h
  have subsetV (a : F) : P a \ C l ⊆ V := fun i hi => mem_compl.mpr (mem_sdiff.mp hi).2
  have outside : (outsideLine fam l).card≤1 := by
    by_contra! many
    obtain ⟨v,hv,w,hw,vw⟩ := one_lt_card.mp many
    have va := (mem_outsideLine_iff fam l v).mp hv
    have wa := (mem_outsideLine_iff fam l w).mp hw
    let l' := secantParameter fam v w
    have hvon := first_point_mem_pointsOn_secant fam (beta:=w) va.1
    have hwon := second_point_mem_pointsOn_secant fam wa.1 vw
    have core : P v ∩ P w=C l' := by
      dsimp only [P,C]
      rw [((mem_pointsOn_iff fam l' v).mp hvon).2,((mem_pointsOn_iff fam l' w).mp hwon).2]
      exact fullAgreement_inter_eq_jointCore D (u 0) (u 1) _ _ vw
    have key := best l' (secantParameter_mem_lineParameters fam va.1 wa.1 vw)
    have inter : (P v \ C l ∩ (P w \ C l)).card ≤ (C l').card := by
      rw [←core]
      exact card_le_card (inter_subset_inter sdiff_subset sdiff_subset)
    have hu := card_le_card (union_subset (subsetV v) (subsetV w))
    have sum := card_union_add_card_inter (P v \ C l) (P w \ C l)
    have c_le := card_le_univ (C l)
    have hv' := fresh hv
    have hw' := fresh hw
    omega
  have partition := pointsOn_card_add_outsideLine_card fam l
  have lineCap := TwoLargeCoreCount.line_occupancy_le fam hn ht hl
  obtain ⟨v,hv⟩ := card_pos.mp (by omega : 0<(outsideLine fam l).card)
  have cv := (fresh hv).trans (card_le_card (subsetV v))
  have c_le := card_le_univ (C l)
  have width : 2≤t-(C l).card := by omega
  have pack := pointsOn_card_mul_max_add_core_le fam hl
  rw [ht,hn] at pack
  change (pointsOn fam l).card * max 1 (t-(C l).card)+(C l).card≤e+t at pack
  rw [max_eq_right (by omega)] at pack
  have two := two_le_pointsOn_card_of_mem_lineParameters fam hl
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (pointsOn fam l).card≠0)
  rw [hr,Nat.succ_mul] at pack
  have := Nat.mul_le_mul_left r width
  omega

/-- The spike has exactly the worst possible probability on every finite-field
domain throughout the range of the maximal-core argument. -/
theorem mass {F : Type} [Field F] [Fintype F] {n k e : ℕ} [NeZero n] (D : Fin n ↪ F)
    (hk : 2≤k) (room : 2*(e+k-1)<n) :
    epsMCA (F:=F) (ReedSolomon.code D k : Set (Fin n → F)) ((e:ℝ≥0)/n) =
      ((e+1:ℕ):ℝ≥0∞)/Fintype.card F := by
  classical
  have hn : (n:ℝ≥0)≠0 := by exact_mod_cast NeZero.ne n
  apply le_antisymm
  · apply epsMCA_le_of_badCount_le
    intro u
    let fam := canonicalBadScalarRichPointFamily D ((e:ℝ≥0)/n) u (by omega : 1≤k)
    apply family_bound (t:=n-e) fam hk (by rw [Fintype.card_fin];omega) _ (by simpa using room)
    rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ hn,←Nat.cast_tsub,Nat.ceil_natCast]
  · rw [← BoundarySecurityBudget.rsCode_eq_code]
    let pos : Fin (e+1) ↪ Fin n := Fin.castLEEmb (by omega)
    exact SpikeFloor.epsMCA_ge_j_div_card (j:=e+1) (SpikeFloor.rsCode D k)
      (SpikeFloor.rsCode_noWeightLE D (by omega))
      (by simp [Fintype.card_fin,div_mul_cancel₀ _ hn]) (by omega) (by rw [Fintype.card_fin];omega)
      pos (pos.trans D) (b:=(1:F)) one_ne_zero

/-- For dimension two and odd length, the odd-redundancy predecessor has
exact numerator h on every domain and for both parities of h. -/
theorem dimension_two {F : Type} [Field F] [Fintype F] {n h : ℕ} [NeZero n] (D : Fin n ↪ F)
    (length : n=2*h+1) (pos : 0<h) :
    epsMCA (F:=F) (ReedSolomon.code D 2 : Set (Fin n → F)) (((h-1:ℕ):ℝ≥0)/n) =
      (h:ℝ≥0∞)/Fintype.card F := by
  simpa only [show h-1+1=h by omega] using mass (e:=h-1) D (by decide : 2≤2) (by omega)

/-- On every odd-length dimension-two code, all budgets through 2h+1 first
fail at min(B,h), including the odd budget B=h. -/
theorem dimension_two_plateau {F : Type} [Field F] [Fintype F] {n h B Q : ℕ} [NeZero n]
    (D : Fin n ↪ F) (length : n=2*h+1) (large : 2≤h) (two : 2≤Q)
    (budget : Fintype.card F/Q=B) (cap : B≤2*h+1) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code D 2 : Set (Fin n → F)) ^⋈ (Fin width)
    let r : ℝ≥0 := ((min B h:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=F) C (1/(Q:ℝ≥0∞))=r ∧ ∀ δ, epsMCA (F:=F) C δ ≤ 1/(Q:ℝ≥0∞) ↔ δ<r := by
  classical
  let C := (ReedSolomon.code D 2 : Set (Fin n → F))
  let j := min B h
  let r : ℝ≥0 := (j:ℝ≥0)/n
  have ratio (i : ℕ) : ((i:ℝ≥0∞)/Fintype.card F ≤ 1/(Q:ℝ≥0∞)) ↔ i≤B := by
    rw [←budget]
    exact BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by omega)
  have fail : 1/(Q:ℝ≥0∞)<epsMCA (F:=F) C r := by
    dsimp only [C,r,j]
    by_cases low : B<h
    · rw [min_eq_left low.le,mass D (by decide) (by omega)]
      exact lt_of_not_ge (fun h => (by omega : ¬B+1≤B) ((ratio _).mp h))
    · rw [min_eq_right (by omega : h≤B)]
      have hq : B<Fintype.card F := budget ▸ Nat.div_lt_self Fintype.card_pos (by omega)
      have lower := UniversalTwoHeadBudget.mass D (e:=h) (by decide : 2≤2)
        (by rw [Fintype.card_fin];omega) (by rw [Fintype.card_fin];omega)
      rw [Fintype.card_fin] at lower
      exact lt_of_lt_of_le (lt_of_not_ge (fun safe => (lt_min hq (by omega : B<2*(h+1))).not_ge
        ((ratio _).mp safe))) lower
  have result : mcaDeltaStar (F:=F) C (1/(Q:ℝ≥0∞))=r := by
    by_cases zero : j=0
    · exact le_antisymm (mcaDeltaStar_le_of_bad C _ fail) (by simp [r,zero])
    have jh : j≤h := min_le_right ..
    have jb : j≤B := min_le_left ..
    apply MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad (a:=j)
      (by omega) (by omega) C _ _ fail
    exact (mass (e:=j-1) D (by decide) (by omega)).le.trans ((ratio _).mpr (by omega))
  dsimp only
  rw [mcaDeltaStar_interleaved_eq]
  refine ⟨result,?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro safe
    by_contra! above
    exact fail.not_ge ((epsMCA_mono C above).trans safe)
  · intro below
    by_contra! bad
    have bound := mcaDeltaStar_le_of_bad C _ bad
    rw [result] at bound
    exact below.not_ge bound

end ProximityGap.MaximalSecantCore
#print axioms ProximityGap.MaximalSecantCore.mass
#print axioms ProximityGap.MaximalSecantCore.dimension_two
#print axioms ProximityGap.MaximalSecantCore.dimension_two_plateau
