/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadDeterminantCover
import ArkLib.Research.ProximityGap.Frontier.FourHeadCoreDeterminant

/-! # Five polynomial heads in general position at the production predecessors -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.FiveHeadTrianglePacking
open HalfPredecessorRateQuarterDeterminantMultiplicity HalfPredecessorLineCoreGeometry
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines

/-- All ten triples of a five-element set, with increasing entries. -/
def triangle : Fin 10 → Fin 3 → Fin 5 :=
  ![![0,1,2],![0,1,3],![0,1,4],![0,2,3],![0,2,4],![0,3,4],
    ![1,2,3],![1,2,4],![1,3,4],![2,3,4]]

private def bit (b : Fin 5 → Bool) (i : Fin 5) : ℕ := if b i then 1 else 0
private def charge (b : Fin 5 → Bool) (j : Fin 10) : ℕ :=
  bit b (triangle j 0)+bit b (triangle j 1)+bit b (triangle j 2)-1

private theorem local_count : ∀ b : Fin 5 → Bool,
    3*(∑ i, bit b i) ≤ 3+∑ j, charge b j ∧
    5*(∑ i, bit b i) ≤ 7+∑ j, charge b j := by decide

variable {I F : Type} [Fintype I] [Field F] [DecidableEq F]

/-- Core incidence bounds from all ten determinants. The local charges when
zero through five heads agree are respectively 0, 0, 3, 8, 14 and 20. -/
theorem incidence (dom : I ↪ F) (u v : I → F) (L : Fin 5 → F[X] × F[X]) (k : ℕ)
    (hdeg : ∀ i, (L i).1.natDegree<k ∧ (L i).2.natDegree<k)
    (hdet : ∀ j, threeLineDeterminant (L (triangle j 0)) (L (triangle j 1)) (L (triangle j 2))≠0) :
    let total := ∑ i, (jointCore dom u v (L i).1 (L i).2).card
    3*total ≤ 3*Fintype.card I+10*(2*k-2) ∧
      5*total ≤ 7*Fintype.card I+10*(2*k-2) := by
  classical
  let b (x : I) (i : Fin 5) := decide (AgreesAt (u x) (v x) (dom x) (L i))
  have one (i : Fin 5) : ∑ x, bit (b x) i = (jointCore dom u v (L i).1 (L i).2).card := by
    simp [bit,b,AgreesAt,jointCore]
    congr 1
    apply filter_congr
    intro x _
    exact @decide_eq_true_iff (AgreesAt (u x) (v x) (dom x) (L i)) (Classical.propDecidable _)
  have all : (∑ x, ∑ i, bit (b x) i) = ∑ i, (jointCore dom u v (L i).1 (L i).2).card := by
    rw [sum_comm]; simp_rw [one]
  have tri (j : Fin 10) : ∑ x, charge (b x) j ≤ 2*k-2 := by
    have h := sum_coreCount_sub_one_le_natDegree dom u v _ _ _ univ (hdet j)
    have hd := natDegree_threeLineDeterminant_le_two_mul_sub_two
      (hdeg (triangle j 0)).1 (hdeg (triangle j 0)).2
      (hdeg (triangle j 1)).1 (hdeg (triangle j 1)).2
      (hdeg (triangle j 2)).1 (hdeg (triangle j 2)).2
    simpa [charge,bit,b,coreCount] using h.trans hd
  have budget : (∑ x, ∑ j, charge (b x) j) ≤ 10*(2*k-2) := by
    rw [sum_comm]
    exact (sum_le_sum (s:=univ) fun j _ => tri j).trans_eq (by simp)
  have h₁ := sum_le_sum (s:=univ) (fun x _ => (local_count (b x)).1)
  have h₂ := sum_le_sum (s:=univ) (fun x _ => (local_count (b x)).2)
  rw [← mul_sum,sum_add_distrib,all] at h₁ h₂
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at h₁ h₂
  dsimp only
  omega

/-- Omitting one head and ordering the four that remain. -/
def four (q : Fin 5) (e : Equiv.Perm (Fin 4)) (i : Fin 4) := q.succAbove (e i)

private def selected (b : Fin 5 → Bool) (q : Fin 5) : Finset (Fin 4) :=
  univ.filter fun j => b (q.succAbove j)

private theorem local_four : ∀ b : Fin 5 → Bool,
    3*(∑ i, bit b i) ≤ 3+∑ q, _root_.ProximityGap.FourHeadCoreDeterminant.charge (selected b q).card := by
  decide

/-- Summing the five four-head minors gives the first bound as soon as each
four-subset contains a noncollinear triple. Collinear triples are allowed. -/
theorem four_incidence (dom : I ↪ F) (u v : I → F) (L : Fin 5 → F[X] × F[X]) (d : ℕ)
    (hinj : Function.Injective L) (hdeg : ∀ i, (L i).1.natDegree≤d ∧ (L i).2.natDegree≤d)
    (hdet : ∀ q, ∃ e, threeLineDeterminant (L (four q e 0)) (L (four q e 1)) (L (four q e 2))≠0) :
    3*(∑ i, (jointCore dom u v (L i).1 (L i).2).card) ≤ 3*Fintype.card I+20*d := by
  classical
  let b (x : I) (i : Fin 5) := decide (AgreesAt (u x) (v x) (dom x) (L i))
  let W (x : I) (q : Fin 5) := _root_.ProximityGap.FourHeadCoreDeterminant.charge (selected (b x) q).card
  have one (i : Fin 5) : ∑ x, bit (b x) i = (jointCore dom u v (L i).1 (L i).2).card := by
    simp [bit,b,AgreesAt,jointCore]
    congr 1
    apply filter_congr
    intro x _
    exact @decide_eq_true_iff (AgreesAt (u x) (v x) (dom x) (L i)) (Classical.propDecidable _)
  have all : (∑ x, ∑ i, bit (b x) i) = ∑ i, (jointCore dom u v (L i).1 (L i).2).card := by
    rw [sum_comm]; simp_rw [one]
  have part (q : Fin 5) : (∑ x, W x q) ≤ 4*d := by
    obtain ⟨e,he⟩ := hdet q
    let A (i : Fin 4) := (L (four q e i)).1
    let B (i : Fin 4) := (L (four q e i)).2
    let S (x : I) := (selected (b x) q).map e.symm.toEmbedding
    have distinct (i : Fin 3) : (A 3,B 3)≠(A i.castSucc,B i.castSucc) := by
      intro h
      have eq : 3=i.castSucc := e.injective (Fin.succAbove_right_injective (hinj h))
      have v := congrArg Fin.val eq
      change 3=i.val at v
      omega
    have h := _root_.ProximityGap.FourHeadCoreDeterminant.sum_charge_le dom u v A B d
      (fun i => (hdeg _).1) (fun i => (hdeg _).2) he distinct S (by
        intro x i hi
        obtain ⟨j,hj,rfl⟩ := mem_map.mp hi
        have hz : AgreesAt (u x) (v x) (dom x) (L (q.succAbove j)) := of_decide_eq_true (mem_filter.mp hj).2
        simpa only [A,B,four,AgreesAt,Equiv.coe_toEmbedding,Equiv.apply_symm_apply] using hz)
    simpa only [S,card_map,W] using h
  have budget : (∑ x, ∑ q, W x q) ≤ 20*d := by
    rw [sum_comm]
    exact (sum_le_sum (s:=univ) fun q _ => part q).trans_eq (by simp; omega)
  have count := sum_le_sum (s:=univ) (fun x _ => local_four (b x))
  change (∑ x, 3*∑ i, bit (b x) i) ≤ ∑ x, (3+∑ q, W x q) at count
  rw [← mul_sum,sum_add_distrib,all] at count
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at count
  omega

variable [DecidableEq I] [Nonempty I] [Fintype F]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- At the second-prime quarter-rate predecessor, any five secants of population
at least 119 include a collinear triple, on every field and evaluation domain. -/
theorem quarter (fam : BadScalarRichPointFamily dom 268435456 δ u)
    (hn : Fintype.card I=1073741824) (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=520093696)
    (L : Fin 5 → LineParameter F) (hl : ∀ i, L i∈lineParameters fam)
    (hbig : ∀ i, 119≤(pointsOn fam (L i)).card) :
    ∃ j, threeLineDeterminant (L (triangle j 0)) (L (triangle j 1)) (L (triangle j 2))=0 := by
  classical
  by_contra! hdet
  have hu := (incidence dom (u 0) (u 1) L _ (fun i => lineParameter_degree_lt fam (hl i)) hdet).2
  rw [hn] at hu
  let C (i : Fin 5) := (jointCore dom (u 0) (u 1) (L i).1 (L i).2).card
  have big (i : Fin 5) : 515396075 ≤ C i := by
    have h := pointsOn_card_mul_max_add_core_le fam (hl i)
    rw [ht,hn] at h
    change (pointsOn fam (L i)).card*max 1 (520093696-C i)+C i ≤ _ at h
    have hm := Nat.mul_le_mul (hbig i) (Nat.le_max_right 1 (520093696-C i))
    omega
  have tot := sum_le_sum (s:=univ) fun i _ => big i
  change 5*(∑ i, C i) ≤ _ at hu
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at tot
  omega

/-- At the eighth-rate predecessor any five distinct rich heads of population
at least 1,216 have a four-head subset for which every triple is collinear. -/
theorem eighth (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I=1073741824) (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=394264576)
    (L : Fin 5 → LineParameter F) (hinj : Function.Injective L) (hl : ∀ i, L i∈lineParameters fam)
    (hbig : ∀ i, 1216≤(pointsOn fam (L i)).card) :
    ∃ q, ∀ e, threeLineDeterminant (L (four q e 0)) (L (four q e 1)) (L (four q e 2))=0 := by
  classical
  by_contra! hdet
  have deg (i : Fin 5) := lineParameter_degree_lt fam (hl i)
  have hu := four_incidence dom (u 0) (u 1) L 134217727 hinj
    (fun i => ⟨Nat.le_of_lt_succ (deg i).1,Nat.le_of_lt_succ (deg i).2⟩) hdet
  rw [hn] at hu
  let C (i : Fin 5) := (jointCore dom (u 0) (u 1) (L i).1 (L i).2).card
  have big (i : Fin 5) : 393705335 ≤ C i := by
    have h := pointsOn_card_mul_max_add_core_le fam (hl i)
    rw [ht,hn] at h
    change (pointsOn fam (L i)).card*max 1 (394264576-C i)+C i ≤ _ at h
    have hm := Nat.mul_le_mul (hbig i) (Nat.le_max_right 1 (394264576-C i))
    omega
  have tot := sum_le_sum (s:=univ) fun i _ => big i
  change 3*(∑ i, C i) ≤ _ at hu
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at tot
  omega

omit [DecidableEq F] [Fintype F] in
private theorem same_line {a b c x : F[X] × F[X]} (hca : c≠a)
    (hcol : threeLineDeterminant a b c=0) (hout : threeLineDeterminant a b x≠0) :
    threeLineDeterminant a c x≠0 := by
  intro h
  apply hca
  have hx : (c.1-a.1)*threeLineDeterminant a b x=0 := by
    unfold threeLineDeterminant at *
    linear_combination (b.1-a.1)*h+(x.1-a.1)*hcol
  have hy : (c.2-a.2)*threeLineDeterminant a b x=0 := by
    unfold threeLineDeterminant at *
    linear_combination (b.2-a.2)*h+(x.2-a.2)*hcol
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right hout))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_right hout))

omit [DecidableEq F] [Fintype F] in
private theorem swap_det (a b c : F[X] × F[X]) :
    threeLineDeterminant b a c = -threeLineDeterminant a b c := by
  unfold threeLineDeterminant
  ring

/-- Once three rich heads are collinear, at most one further rich head can lie
off their common line. Thus any collection of at least five rich heads has a
single line containing all but at most one of them. -/
theorem eighth_outlier (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I=1073741824) (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=394264576)
    (L : Fin 5 → LineParameter F) (hinj : Function.Injective L) (hl : ∀ i, L i∈lineParameters fam)
    (hbig : ∀ i, 1216≤(pointsOn fam (L i)).card) (hcol : threeLineDeterminant (L 0) (L 1) (L 2)=0) :
    threeLineDeterminant (L 0) (L 1) (L 3)=0 ∨ threeLineDeterminant (L 0) (L 1) (L 4)=0 := by
  by_contra! h
  have hcol' : threeLineDeterminant (L 1) (L 0) (L 2)=0 := by rw [swap_det,hcol,neg_zero]
  have h03 := same_line (hinj.ne (by decide : (2:Fin 5)≠0)) hcol h.1
  have h13 := same_line (hinj.ne (by decide : (2:Fin 5)≠1)) hcol' (x:=L 3)
    (by rw [swap_det]; exact neg_ne_zero.mpr h.1)
  obtain ⟨q,hq⟩ := eighth fam hn ht L hinj hl hbig
  fin_cases q
  · exact h13 (hq (Equiv.refl _))
  · exact h03 (hq (Equiv.refl _))
  · exact h.1 (hq (Equiv.refl _))
  · exact h.2 (hq (Equiv.swap 2 3))
  · exact h.1 (hq (Equiv.swap 2 3))

#print axioms eighth_outlier
#print axioms incidence
#print axioms quarter
#print axioms eighth
end ArkLib.ProximityGap.Frontier.FiveHeadTrianglePacking
