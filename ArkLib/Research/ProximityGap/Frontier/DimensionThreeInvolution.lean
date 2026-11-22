/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DimensionThreePairCriterion

/-! # A projective involution forced by a dimension-three endpoint overrun -/

namespace ProximityGap.DimensionThreeInvolution
open Polynomial Finset DimensionThreePairCriterion MCAThresholdLedger ArkLib.ProximityGap.Frontier
open scoped NNReal ENNReal
variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- The off-diagonal equation of a nondegenerate projective involution carrying
each evaluation site to another evaluation site. -/
def Reflects (D : I ↪ F) : Prop := ∃ a b c : F, a*c ≠ b^2 ∧
  ∀ i, ∃ j, i≠j ∧ a*D i*D j+b*(D i+D j)+c=0

omit [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I] in
private theorem determinant (P Q : F[X]) (hp : P.natDegree<3) (hq : Q.natDegree<3) (x y : F) :
    P.eval x*Q.eval y-P.eval y*Q.eval x = (x-y)*
      ((P.coeff 2*Q.coeff 1-P.coeff 1*Q.coeff 2)*x*y+
       (P.coeff 2*Q.coeff 0-P.coeff 0*Q.coeff 2)*(x+y)+
       (P.coeff 1*Q.coeff 0-P.coeff 0*Q.coeff 1)) := by
  rw [P.eval_eq_sum_range' hp,P.eval_eq_sum_range' hp,Q.eval_eq_sum_range' hq,Q.eval_eq_sum_range' hq]
  simp only [sum_range_succ,sum_range_zero,pow_zero,mul_one,pow_one,zero_add]
  ring

omit [Nonempty I] [Fintype F] in
/-- The algebraic criterion on the quadratic ratio forces a single involution
of the projective line to exchange all the evaluation pairs. -/
theorem necessary (D : I ↪ F) {h : ℕ} (length : Fintype.card I=2*h+2) (large : 1≤h)
    (yes : Paired D h) : Reflects D := by
  classical
  obtain ⟨P,Q,hp,hq,S,sz,fib⟩ := yes
  obtain ⟨G,hGS,hG⟩ := exists_subset_card_eq (by omega : h+1≤S.card)
  let A := P.coeff 2*Q.coeff 1-P.coeff 1*Q.coeff 2
  let B := P.coeff 2*Q.coeff 0-P.coeff 0*Q.coeff 2
  let C := P.coeff 1*Q.coeff 0-P.coeff 0*Q.coeff 1
  let val := fiber D P Q
  have eq (i j : I) : P.eval (D i)*Q.eval (D j)-P.eval (D j)*Q.eval (D i)=
        (D i-D j)*(A*D i*D j+B*(D i+D j)+C) := determinant P Q hp hq _ _
  have val_in {z : F} {i : I} (hi : i∈val z) := (mem_filter.mp hi).2
  have dis {z w : F} (zw : z≠w) : Disjoint (val z) (val w) := by
    intro T hT hT' x hx
    obtain ⟨nz,first⟩ := val_in (hT hx)
    exact (zw (mul_right_cancel₀ nz (first.symm.trans (val_in (hT' hx)).2))).elim
  have count : (G.biUnion val).card=Fintype.card I := by
    apply le_antisymm (card_le_univ _)
    rw [card_biUnion (fun _ _ _ _ neq => dis neq)]
    have bound := sum_le_sum (s:=G) fun z hz => fib z (hGS hz)
    simpa only [sum_const,nsmul_eq_mul,Nat.cast_id,hG,length,add_mul,one_mul,mul_comm] using bound
  have cover := (G.biUnion val).eq_univ_of_card count
  have form {z : F} {i j : I} (ij : i≠j) (hi : i∈val z) (hj : j∈val z) :
      A*D i*D j+B*(D i+D j)+C=0 := by
    have product : (D i-D j)*(A*D i*D j+B*(D i+D j)+C)=0 := by
      rw [←eq,(val_in hi).2,(val_in hj).2];ring
    exact (mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr (D.injective.ne ij))
  obtain ⟨z,hz,w,hw,zw⟩ := one_lt_card.mp (by omega : 1<G.card)
  obtain ⟨i,hi,j,hj,ij⟩ := one_lt_card.mp (fib z (hGS hz))
  obtain ⟨v,hv,y,hy,vy⟩ := one_lt_card.mp (fib w (hGS hw))
  have ijEq := form ij hi hj
  have vyEq := form vy hv hy
  refine ⟨A,B,C,?_,?_⟩
  · intro singular
    by_cases zero : A=0
    · have zb : B=0 := by simpa [zero] using singular.symm
      have zc : C=0 := by simpa [zero,zb] using ijEq
      obtain ⟨ni,ei⟩ := val_in hi
      obtain ⟨nv,ev⟩ := val_in hv
      have equality := eq i v
      rw [zero,zb,zc,ei,ev] at equality
      have cross : (z-w)*(Q.eval (D i)*Q.eval (D v))=0 := by linear_combination equality
      exact (mul_ne_zero (sub_ne_zero.mpr zw) (mul_ne_zero ni nv)) cross
    · have zap {x y : I} (e : A*D x*D y+B*(D x+D y)+C=0) :
          A*D x+B=0 ∨ A*D y+B=0 := by
        apply mul_eq_zero.mp
        linear_combination A*e-singular
      have no {x y : I} (xZ : x∈val z) (yW : y∈val w) (ex : A*D x+B=0) (ey : A*D y+B=0) : False := by
        have same := D.injective (mul_left_cancel₀ zero (add_right_cancel (ex.trans ey.symm)))
        exact disjoint_left.mp (dis zw) (same ▸ xZ) yW
      rcases zap ijEq with ex|ex <;> rcases zap vyEq with ey|ey
      · exact no hi hv ex ey
      · exact no hi hy ex ey
      · exact no hj hv ex ey
      · exact no hj hy ex ey
  · intro x
    obtain ⟨z,hz,hx⟩ := mem_biUnion.mp (cover ▸ (mem_univ x))
    obtain ⟨v,hv,y,hy,vy⟩ := one_lt_card.mp (fib z (hGS hz))
    by_cases xv : x=v
    · exact ⟨y,xv ▸ vy,form (xv ▸ vy) hx hy⟩
    · exact ⟨v,xv,form xv hx hv⟩

omit [Nonempty I] [Fintype F] in
/-- Conversely the invariant rational function of the involution has precisely
two finite sites per attained value. This includes involutions without field-
rational fixed points. -/
theorem sufficient (D : I ↪ F) {h : ℕ} (length : Fintype.card I=2*h+2)
    (reflects : Reflects D) : Paired D h := by
  classical
  obtain ⟨a,b,c,nonsing,partners⟩ := reflects
  have den (i : I) : a*D i+b≠0 := by
    intro zero
    obtain ⟨j,_,rel⟩ := partners i
    apply nonsing
    linear_combination a*rel-(a*D j+b)*zero
  obtain ⟨s,t,st⟩ : ∃ s t : F, b*s-a*t=c := by
    by_cases nb : b=0
    · have na : a≠0 := by intro za;simp [nb,za] at nonsing
      exact ⟨0,-c/a,by field_simp;ring⟩
    exact ⟨c/b,0,by field_simp;ring⟩
  let P : F[X] := (Polynomial.X : F[X])^2+Polynomial.C s*Polynomial.X+Polynomial.C t
  let Q : F[X] := Polynomial.C a*Polynomial.X+Polynomial.C b
  have pe (x : F) : P.eval x=x^2+s*x+t := by simp [P]
  have qe (x : F) : Q.eval x=a*x+b := by simp [Q]
  let z (i : I) := P.eval (D i)/Q.eval (D i)
  let G := univ.image z
  have nz (i : I) : Q.eval (D i)≠0 := qe _ ▸ den i
  have equiv (i j : I) (ij : i≠j) :
      z i=z j ↔ a*D i*D j+b*(D i+D j)+c=0 := by
    change _/_=_/_ ↔ _
    rw [div_eq_div_iff (nz i) (nz j),←sub_eq_zero,pe,pe,qe,qe]
    have e : ((D i)^2+s*D i+t)*(a*D j+b)-((D j)^2+s*D j+t)*(a*D i+b)=
        (D i-D j)*(a*D i*D j+b*(D i+D j)+c) := by linear_combination (D i-D j)*st
    rw [e,mul_eq_zero,or_iff_right (sub_ne_zero.mpr (D.injective.ne ij))]
  have pairs (y : F) (hy : y∈G) : (univ.filter fun i => z i=y).card=2 := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp hy
    obtain ⟨j,ij,rel⟩ := partners i
    have same := (equiv i j ij).mpr rel
    have eq : univ.filter (fun v => z v=z i)={i,j} := by
      ext v
      simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
      constructor
      · intro hv
        by_cases vi : v=i
        · exact Or.inl vi
        apply Or.inr
        have rel' := (equiv i v (Ne.symm vi)).mp hv.symm
        apply D.injective
        apply mul_left_cancel₀ (den i)
        linear_combination rel'-rel
      · rintro (rfl|rfl)
        · rfl
        · exact same.symm
    simp [eq,ij]
  have total := card_eq_sum_card_fiberwise (s:=(univ : Finset I)) (t:=G) (f:=z)
    (fun i hi => mem_image_of_mem z hi)
  simp only [card_univ] at total
  have sum : ∑ y ∈ G,(univ.filter fun i => z i=y).card=G.card*2 := by
    calc
      _ = ∑ _y ∈ G, 2 := sum_congr rfl pairs
      _ = _ := by simp
  have pdeg : P.natDegree<3 := by dsimp only [P];compute_degree!
  have qdeg : Q.natDegree<3 := by dsimp only [Q];compute_degree!
  refine ⟨P,Q,pdeg,qdeg,G,by omega,?_⟩
  intro y hy
  have eq : fiber D P Q y=univ.filter fun i => z i=y := by
    ext i
    simp [fiber,z,nz,div_eq_iff]
  rw [eq,pairs y hy]

omit [Nonempty I] [Fintype F] in
/-- A domain has the requisite quadratic fibers exactly when it is a union
of full two-element orbits of one projective involution. -/
theorem iff_reflects (D : I ↪ F) {h : ℕ} (length : Fintype.card I=2*h+2) (large : 1≤h) :
    Paired D h ↔ Reflects D := ⟨necessary D length large,sufficient D length⟩

/-- The symmetry predicate uses only finite field and finite site quantifiers. -/
instance decidableReflects (D : I ↪ F) : Decidable (Reflects D) := by
  unfold Reflects
  infer_instance

/-- The operational first failure at the exceptional budget is selected by a
finite symmetry test on the supplied domain, at every positive width. -/
theorem classification {n h Q : ℕ} [NeZero n] (D : Fin n ↪ F) (length : n=2*h+2)
    (large : 4≤h) (odd : h%2=1) (security : 0<Q) (budget : Fintype.card F/Q=h)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code D 3 : Set (Fin n → F)) ^⋈ (Fin width)
    let r : ℝ≥0 := ((if Reflects D then h-1 else h : ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=F) C (1/(Q:ℝ≥0∞))=r ∧ ∀ δ, epsMCA (F:=F) C δ≤1/(Q:ℝ≥0∞) ↔ δ<r := by
  classical
  by_cases yes : Reflects D
  · dsimp only
    rw [ite_eq_left yes]
    apply OddRedundancyApolar.exceptional_of_lower D (by decide) (by omega)
      (by omega : n=3+2*h-1) large security budget _ width
    simpa only [Fintype.card_fin] using DimensionThreePairCriterion.sufficient D
      (by simpa using length) (by omega) odd (sufficient D (by simpa using length) yes)
  dsimp only
  rw [ite_eq_right yes]
  let C := (ReedSolomon.code D 3 : Set (Fin n → F))
  have ratio (m : ℕ) : ((m:ℝ≥0∞)/Fintype.card F≤1/(Q:ℝ≥0∞)) ↔ m≤h :=
    budget ▸ BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos security
  have fail : 1/(Q:ℝ≥0∞)<epsMCA (F:=F) C ((h:ℝ≥0)/n) := by
    have lower := TwoHeadLinearBudget.errors (e:=h) (k:=3) D
      (by rw [Fintype.card_fin];omega) (by rw [Fintype.card_fin];omega) (by rw [Fintype.card_fin];omega)
    rw [Fintype.card_fin] at lower
    exact lt_of_lt_of_le (lt_of_not_ge (fun safe => (by omega : ¬2*(h+1)≤h) ((ratio _).1 safe))) lower
  have good := DimensionThreePairCriterion.mass D length large odd
  rw [ite_eq_right (fun paired => yes (necessary D (by simpa using length) (by omega) paired))] at good
  have result := MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
    (a:=h) (by omega) (by omega) C _ (good.le.trans ((ratio _).2 le_rfl)) fail
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

end ProximityGap.DimensionThreeInvolution
#print axioms ProximityGap.DimensionThreeInvolution.necessary
#print axioms ProximityGap.DimensionThreeInvolution.iff_reflects
#print axioms ProximityGap.DimensionThreeInvolution.classification
