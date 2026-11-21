/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SixteenthSaturatedHeads

/-! # Third secants from agreements on the complement of two nearly full cores -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal ENNReal
open _root_.ProximityGap
namespace ArkLib.ProximityGap.Frontier.ThirdHeadComplement
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines HalfPredecessorLineCoreGeometry
open HalfPredecessorRateEighthFullWiring HalfPredecessorRateQuarterComplementaryCores
open HalfPredecessorRateQuarterDeterminantMultiplicity HalfPredecessorRateQuarterPrimitiveDirection
open HalfPredecessorRateQuarterDeterminantCollapse ThreeHeadDeterminantCover TerminalCollinearHeadCount
open SecondPrimeActualPopulations _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger TerminalDomainSecurity
variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- An outsider loses at most twice the message degree to two joint cores. -/
private theorem outside_agreements {k t : ℕ} (fam : BadScalarRichPointFamily dom k δ u)
    (hk : 1≤k) (ht : t≤⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊)
    {a b : LineParameter F} (ha : a∈lineParameters fam) (hb : b∈lineParameters fam)
    {z : F} (hz : z∈fam.G \ (pointsOn fam a ∪ pointsOn fam b)) :
    let O := univ \ (jointCore dom (u 0) (u 1) a.1 a.2 ∪ jointCore dom (u 0) (u 1) b.1 b.2)
    let S := fullAgreement dom (u 0) (u 1) z (fam.q z)
    t ≤ (O ∩ S).card + 2*(k-1) := by
  classical
  let D (l : LineParameter F) := jointCore dom (u 0) (u 1) l.1 l.2
  let O := univ \ (D a ∪ D b)
  let S := fullAgreement dom (u 0) (u 1) z (fam.q z)
  have hzg := (mem_sdiff.mp hz).1
  have cap (l : LineParameter F) (hl : l∈lineParameters fam) (h : z∉pointsOn fam l) :
      (S ∩ D l).card≤k-1 := by
    have hd := lineParameter_degree_lt fam hl
    exact fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk (fam.degree_lt z hzg) hd.1 hd.2
      (fun eq => h ((mem_pointsOn_iff fam l z).mpr ⟨hzg,eq⟩))
  have ca := cap a ha (fun h => (mem_sdiff.mp hz).2 (mem_union_left _ h))
  have cb := cap b hb (fun h => (mem_sdiff.mp hz).2 (mem_union_right _ h))
  have hsub : S ⊆ ((S ∩ D a) ∪ (S ∩ D b)) ∪ (O ∩ S) := by
    intro i hi
    by_cases h : i∈D a
    · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hi,h⟩))
    by_cases j : i∈D b
    · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hi,j⟩))
    exact mem_union_right _ (mem_inter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,by simp [h,j]⟩,hi⟩)
  have bound := (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _))
  have lo : t ≤ S.card := ht.trans (fam.threshold_le z hzg)
  change t ≤ (O ∩ S).card+2*(k-1)
  omega

/-- The full deficit bound uses a third actual secant even if it has only two witnesses. -/
theorem family_cap (fam : Family dom δ u) {p e x : ℕ} [CharP F p] (hp : 1744830589<p)
    (hn : Fintype.card I=1073741824) (he : e+x=671088640) (hx : 0<x) (hl : 610000000≤e)
    (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=1073741824-e) :
    fam.G.card≤2*(e+1)+(1+e/(3*x)) := by
  classical
  by_contra! large
  have nonneg : 0 ≤ e/(3*x) := Nat.zero_le _
  have strict : 2*(e+1)+1 < fam.G.card := lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right 1 (e/(3*x))) _) large
  obtain ⟨a,ha,b,hb,hab,_,_,hA,hB⟩ := SixteenthSaturatedHeads.near_full_pair fam hp hn hl
    (by omega) ht (by omega)
  let D (l : LineParameter F) := jointCore dom (u 0) (u 1) l.1 l.2
  let O := univ \ (D a ∪ D b)
  let S (z : F) := fullAgreement dom (u 0) (u 1) z (fam.q z)
  let out := fam.G \ (pointsOn fam a ∪ pointsOn fam b)
  let t := 1073741824-e
  change t-1 ≤ (D a).card at hA
  change t-2 ≤ (D b).card at hB
  have hsum : e+t=1073741824 := by dsimp [t]; omega
  have tmin : t=402653184+x := by dsimp [t]; omega
  have occ (l : LineParameter F) (hl : l∈lineParameters fam) : (pointsOn fam l).card≤e+1 :=
    TwoLargeCoreCount.line_occupancy_le fam (e:=e) (by omega) ht hl
  have inter : (D a ∩ D b).card≤67108863 := jointCore_inter_card_le_degree_pred fam (by decide) ha hb hab
  have hsumAB := card_union_add_card_inter (D a) (D b)
  have unAB := (card_le_univ (D a ∪ D b)).trans_eq hn
  have hO : O.card+(D a ∪ D b).card=1073741824 := by
    dsimp [O]; rw [card_sdiff_of_subset (subset_univ _),card_univ,hn]; omega
  have hG := (card_sdiff_add_card_inter fam.G (pointsOn fam a ∪ pointsOn fam b))
  have hG2 := (card_le_card (inter_subset_right :
    fam.G ∩ (pointsOn fam a ∪ pointsOn fam b) ⊆ _)).trans (card_union_le ..)
  change out.card+_=fam.G.card at hG
  have hpop : 1<out.card := by have := occ a ha; have := occ b hb; omega
  obtain ⟨z,hz,w,hw,hzw⟩ := one_lt_card.mp hpop
  let c := secantParameter fam z w
  have hxG : z∈fam.G := (mem_sdiff.mp hz).1
  have hwG : w∈fam.G := (mem_sdiff.mp hw).1
  have hc : c∈lineParameters fam := secantParameter_mem_lineParameters fam hxG hwG hzw
  have hzc : z∈pointsOn fam c := first_point_mem_pointsOn_secant fam hxG
  have hwc : w∈pointsOn fam c := second_point_mem_pointsOn_secant fam hwG hzw
  have hpair : S z ∩ S w=D c := by
    dsimp only [S,D]
    rw [((mem_pointsOn_iff fam c z).mp hzc).2,((mem_pointsOn_iff fam c w).mp hwc).2]
    exact fullAgreement_inter_eq_jointCore dom (u 0) (u 1) c.1 c.2 hzw
  have miss (v : F) (hv : v∈out) : (O \ S v).card+t ≤ O.card+2*67108863 := by
    have fit := outside_agreements fam (by decide) ht.ge ha hb hv
    change t≤(O ∩ S v).card+2*67108863 at fit
    have h := card_sdiff_add_card_inter O (S v)
    omega
  have uns : O \ D c ⊆ (O \ S z) ∪ (O \ S w) := by
    rw [← hpair]
    grind
  have missing : (O \ D c).card+2*t ≤ 2*O.card+4*67108863 := by
    have h := (card_le_card uns).trans (card_union_le ..)
    have hz' := miss z hz
    have hw' := miss w hw
    omega
  have covered : out ⊆ pointsOn fam c := by
    intro v hv
    by_contra off
    have hvg := (mem_sdiff.mp hv).1
    have hd := lineParameter_degree_lt fam hc
    have cap : (S v ∩ D c).card≤67108863 :=
      fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) (by decide : 1≤67108864)
        (fam.degree_lt v hvg) hd.1 hd.2 (fun eq => off ((mem_pointsOn_iff fam c v).mpr ⟨hvg,eq⟩))
    have sub : O ⊆ ((O \ S v) ∪ (O \ D c)) ∪ (S v ∩ D c) := by grind
    have h := (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _))
    have mm := miss v hv
    omega
  let H : Finset (LineParameter F) := {a,b,c}
  have hH : H⊆lineParameters fam := by
    intro l hl
    simp only [H,mem_insert,mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have cov : fam.G ⊆ H.biUnion (pointsOn fam) := by
    intro v hv
    by_cases a' : v∈pointsOn fam a
    · exact mem_biUnion.mpr ⟨a,by simp [H],a'⟩
    by_cases b' : v∈pointsOn fam b
    · exact mem_biUnion.mpr ⟨b,by simp [H],b'⟩
    exact mem_biUnion.mpr ⟨c,by simp [H],covered (mem_sdiff.mpr ⟨hv,by simp [a',b']⟩)⟩
  by_cases det : ∀ l∈H, lineDeterminant a b l=0
  · have h := collinear_card fam H hH a b hab det
    let U := H.biUnion D
    change (H.biUnion (pointsOn fam)).card ≤ U.card+(Fintype.card I-U.card)*H.card at h
    have sub : univ \ U ⊆ O \ D c := by
      intro i hi
      have hi' := (mem_sdiff.mp hi).2
      exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,fun h => by
        rcases mem_union.mp h with h | h
        · exact hi' (mem_biUnion.mpr ⟨a,by simp [H],h⟩)
        · exact hi' (mem_biUnion.mpr ⟨b,by simp [H],h⟩)⟩,
        fun h => hi' (mem_biUnion.mpr ⟨c,by simp [H],h⟩)⟩
    have rest := card_le_card sub
    rw [card_sdiff_of_subset (subset_univ _),card_univ,hn] at rest
    have size : H.card≤3 := (card_insert_le ..).trans (by
      have h := card_insert_le b ({c}:Finset (LineParameter F))
      simp only [card_singleton] at h
      omega)
    have hnu := (card_le_univ U).trans_eq hn
    rw [hn] at h
    have h' := Nat.mul_le_mul_left (1073741824-U.card) size
    have v := card_le_card cov
    omega
  · have neq : threeLineDeterminant a b c ≠ 0 := by
      intro h
      apply det
      have h' : lineDeterminant a b c=0 := by simpa only [threeLineDeterminant,lineDeterminant,mul_comm] using h
      intro l hl
      simp only [H,mem_insert,mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · simp [lineDeterminant]
      · simp [lineDeterminant]
      · exact h'
    have ha' := lineParameter_degree_lt fam ha
    have hb' := lineParameter_degree_lt fam hb
    have hc' := lineParameter_degree_lt fam hc
    have hdeg := natDegree_threeLineDeterminant_le_two_mul_sub_two ha'.1 ha'.2 hb'.1 hb'.2 hc'.1 hc'.2
    have hbound := core_sum_le_union_add_degree dom (u 0) (u 1) a b c neq
    simp only [coreSet_eq_jointCore] at hbound
    change (D a).card+(D b).card+(D c).card ≤ (D a ∪ D b ∪ D c).card+_ at hbound
    have hnU := (card_le_univ (D a ∪ D b ∪ D c)).trans_eq hn
    have fresh (l : LineParameter F) (h : l∈lineParameters fam) (j : ℕ) (hj : (D l).card+j≤t) :
        ((pointsOn fam l).card-1)*j ≤ e := by
      apply PlateauThreeHeadPredecessor.fresh (by omega : t+e=1073741824) hj
      have pack := pointsOn_card_mul_max_add_core_le fam h
      rwa [ht,hn] at pack
    have count := PlateauThreeHeadPredecessor.count_deficit hx tmin
      (by omega : (D a).card+(D b).card+(D c).card≤1207959550)
      (occ a ha) (occ b hb) (occ c hc) (fresh a ha) (fresh b hb) (fresh c hc)
    have rest := card_le_card covered
    omega

/-- The upper probability bound holds at every interleaving width. -/
theorem eps_upper (dom : I ↪ F) (hn : Fintype.card I=n) {p e x : ℕ} [CharP F p]
    (hp : 1744830589<p) (he : e+x=671088640) (hx : 0<x) (hl : 610000000≤e)
    (width : ℕ) [NeZero width] :
    epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) ≤
      ((2*(e+1)+(1+e/(3*x)):ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  rw [epsMCA_interleaved_eq]
  apply epsMCA_le_of_badCount_le
  intro u
  apply family_cap (canonicalBadScalarRichPointFamily dom (k:=k) ((e:ℝ≥0)/n) u (by decide)) hp hn he hx hl
  rw [hn]
  have h := TwoCorePackingThreshold.agreement_ceiling e (by change e≤1073741824; omega)
  rw [Fintype.card_fin] at h
  exact h

/-- A numeric allowance brackets the first failure for every injective domain
over fields of sufficient characteristic. -/
theorem bracket (dom : I ↪ F) (hn : Fintype.card I=n) {p e x B : ℕ} [CharP F p]
    (hp : 1744830589<p) (he : e+x=671088640) (hx : 0<x) (hl : 610000000≤e)
    (hB : Fintype.card F/2^128=B) (hu : B≤1342177281) (hcap : 2*(e+1)+(1+e/(3*x))≤B)
    (width : ℕ) [NeZero width] :
    let C := ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width))
    ((e+1:ℕ):ℝ≥0)/n ≤ mcaDeltaStar (F:=F) C tolerance ∧
      mcaDeltaStar (F:=F) C tolerance≤((B/2:ℕ):ℝ≥0)/n := by
  dsimp only
  have ratio := (BoundarySecurityBudget.count_ratio_le_iff (Fintype.card_pos (α:=F)) (by decide : 0<2^128)).2
    (hB ▸ hcap : 2*(e+1)+(1+e/(3*x))≤Fintype.card F/2^128)
  have good := (eps_upper dom hn hp he hx hl width).trans (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using ratio : _≤tolerance)
  have hb : 2*(e+1)≤B := (Nat.le_add_right ..).trans hcap
  have bad := ThreeHeadDeficitWindow.two_head_bad dom hn (e:=B/2) (by omega) (by omega) (by omega)
  refine ⟨ThreeHeadDeficitWindow.successor_le_supremum dom hn (by dsimp [n]; omega) width good,?_⟩
  rw [mcaDeltaStar_interleaved_eq]
  exact mcaDeltaStar_le_of_bad _ _ bad

/-- For 8,464,192 budgets just beyond the exact two-head window, the first
failure lies within six Hamming steps of the two-head attack on every smooth domain. -/
theorem six_step_window (dom : I ↪ F) [ReedSolomon.Smooth dom] (hn : Fintype.card I=n)
    {B : ℕ} (hB : Fintype.card F/2^128=B) (hl : 1297438042≤B) (hu : B≤1305902233)
    (width : ℕ) [NeZero width] :
    let C := ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width))
    (((B-12)/2:ℕ):ℝ≥0)/n ≤ mcaDeltaStar (F:=F) C tolerance ∧
      mcaDeltaStar (F:=F) C tolerance≤((B/2:ℕ):ℝ≥0)/n := by
  let e := (B-12)/2-1
  let x := 671088640-e
  have he : 610000000≤e := by dsimp [e]; omega
  have he' : e≤652951109 := by dsimp [e]; omega
  have hx : 0<x := by dsimp [x]; omega
  have hm : e/(3*x)<12 := (Nat.div_lt_iff_lt_mul (by omega : 0<3*x)).2 (by dsimp [x]; omega)
  have h := SmoothCubicCharacteristic.characteristic dom hn (by omega)
  have br := bracket dom hn (p:=ringChar F) (by omega) (e:=e) (x:=x) (by dsimp [x]; omega)
    hx he hB (by omega) (by dsimp [e] at *; omega) width
  rwa [show e+1=(B-12)/2 by dsimp [e]; omega] at br

#print axioms six_step_window
#print axioms eps_upper
#print axioms family_cap
end ArkLib.ProximityGap.Frontier.ThirdHeadComplement
