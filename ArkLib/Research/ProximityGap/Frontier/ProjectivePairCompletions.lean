/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DimensionThreeInvolution

/-! # How many single-site completions can create an involution? -/

namespace ProximityGap.ProjectivePairCompletions
open Finset DimensionThreeInvolution
open scoped NNReal ENNReal
variable {F : Type} [Field F] [DecidableEq F]

/-- The prescribed set is partitioned into pairs of one projective involution. -/
def PairedSet (S : Finset F) : Prop := ∃ a b c : F, a*c≠b^2 ∧
  ∀ u∈S, ∃ v∈S, u≠v ∧ a*u*v+b*(u+v)+c=0

private def partner (a b c z : F) := -(b*z+c)/(a*z+b)

omit [DecidableEq F] in
private theorem partner_eq {a b c z w : F} (valid : a*c≠b^2)
    (eq : a*z*w+b*(z+w)+c=0) : partner a b c z=w := by
  have den : a*z+b≠0 := by
    intro zero
    exact valid (by linear_combination a*eq-(a*w+b)*zero)
  apply (div_eq_iff den).mpr
  linear_combination -eq

private def determined (p : (F × F) × (F × F)) (z : F) : F :=
  let (x,y) := p.1
  let (u,v) := p.2
  partner (x+y-u-v) (u*v-x*y) (x*y*(u+v)-u*v*(x+y)) z

omit [DecidableEq F] in
private theorem determined_eq {a b c x y u v z w : F} (valid : a*c≠b^2)
    (xu : x≠u) (xv : x≠v) (yu : y≠u) (yv : y≠v)
    (xy : a*x*y+b*(x+y)+c=0) (uv : a*u*v+b*(u+v)+c=0)
    (zw : a*z*w+b*(z+w)+c=0) : determined ((x,y),(u,v)) z=w := by
  let A := x+y-u-v
  let B := u*v-x*y
  let C := x*y*(u+v)-u*v*(x+y)
  have nonsing : A*C≠B^2 := by
    rw [←sub_ne_zero]
    have identity : A*C-B^2 = -((x-u)*(x-v)*(y-u)*(y-v)) := by dsimp [A,B,C];ring
    rw [identity]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (sub_ne_zero.mpr xu) (sub_ne_zero.mpr xv)) (sub_ne_zero.mpr yu)) (sub_ne_zero.mpr yv))
  apply partner_eq nonsing
  by_cases na : a=0
  · have nb : b≠0 := by intro zero;simp [na,zero] at valid
    apply mul_left_cancel₀ nb
    dsimp only [A,B,C]
    rw [na] at xy uv zw
    linear_combination (z*w-u*v)*xy - (z*w-x*y)*uv + (u*v-x*y)*zw
  · apply mul_left_cancel₀ na
    dsimp only [A,B,C]
    linear_combination (u+v-z-w)*xy + (z+w-x-y)*uv + (x+y-u-v)*zw

private noncomputable def missing (S : Finset F) (f : F → F) : F :=
  if h : ∃ y∈S.image f, y∉S then h.choose else 0

private theorem missing_eq {S : Finset F} {f : F → F} {x : F}
    (fresh : x∉S) (on : ∀ y∈S, f y∈insert x S) (hit : x∈S.image f) : missing S f=x := by
  have yes : ∃ y∈S.image f, y∉S := ⟨x,hit,fresh⟩
  rw [missing,dite_eq_left yes]
  obtain ⟨present,absent⟩ := yes.choose_spec
  obtain ⟨y,hy,eq⟩ := mem_image.mp present
  exact (mem_insert.mp (eq ▸ on y hy)).resolve_right absent

/-- With four fixed anchors, two disjoint known pairs determine the potential
involution. Its unique image outside the original set determines the new site. -/
theorem completions (S : Finset F) (size : 4≤S.card) :
    ∃ B : Finset F, B.card≤16*S.card^2 ∧ ∀ x∉S, PairedSet (insert x S) → x∈B := by
  classical
  obtain ⟨K,hKS,hK⟩ := exists_subset_card_eq size
  let candidates := (K ×ˢ S) ×ˢ (K ×ˢ S)
  let B := candidates.image fun p => missing S (determined p)
  refine ⟨B,?_,?_⟩
  · apply card_image_le.trans
    simp [candidates,hK]
    nlinarith
  intro x fresh paired
  let T := insert x S
  obtain ⟨a,b,c,valid,hs⟩ := paired
  let f := partner a b c
  have orbit {i : F} (hi : i∈T) : f i∈T ∧ i≠f i ∧ a*i*(f i)+b*(i+f i)+c=0 := by
    obtain ⟨j,hj,ij,rel⟩ := hs i hi
    simpa only [f,partner_eq valid rel] using And.intro hj (And.intro ij rel)
  have inv {i : F} (hi : i∈T) : f (f i)=i := by
    apply partner_eq valid
    linear_combination (orbit hi).2.2
  have hx : x∈T := mem_insert_self ..
  have hsT {i : F} (hi : i∈S) : i∈T := mem_insert_of_mem hi
  let anchors := K.erase (f x)
  have large : 3≤anchors.card := by dsimp only [anchors];have h:=pred_card_le_card_erase (a:=f x) (s:=K);omega
  obtain ⟨u,hu⟩ := card_pos.mp (by omega : 0<anchors.card)
  have fa {i : F} (hi : i∈anchors) : f i∈S := by
    have bound := (orbit (hsT (hKS (mem_erase.mp hi).2))).1
    apply (mem_insert.mp bound).resolve_left
    intro hit
    exact (mem_erase.mp hi).1 ((inv (hsT (hKS (mem_erase.mp hi).2))).symm.trans (congrArg f hit))
  have huK := (mem_erase.mp hu).2
  have huT := hsT (hKS huK)
  obtain ⟨v,hv⟩ : ((anchors.erase u).erase (f u)).Nonempty := by
    apply card_pos.mp
    have h₁ := pred_card_le_card_erase (s:=anchors) (a:=u)
    have h₂ := pred_card_le_card_erase (s:=anchors.erase u) (a:=f u)
    omega
  obtain ⟨vfu,hv'⟩ := mem_erase.mp hv
  obtain ⟨vu,hva⟩ := mem_erase.mp hv'
  have hvK := (mem_erase.mp hva).2
  have hvT := hsT (hKS hvK)
  have different : f u≠f v := fun eq => vu ((inv hvT).symm.trans ((congrArg f eq.symm).trans (inv huT)))
  have cross : u≠f v := fun eq => vfu ((inv hvT).symm.trans (congrArg f eq.symm))
  let p := ((u,f u),(v,f v))
  have agrees {y : F} (hy : y∈T) : determined p y=f y :=
    determined_eq valid vu.symm cross vfu.symm different
      (orbit huT).2.2 (orbit hvT).2.2 (orbit hy).2.2
  apply mem_image.mpr
  refine ⟨p,mem_product.mpr ⟨mem_product.mpr ⟨huK,fa hu⟩,mem_product.mpr ⟨hvK,fa hva⟩⟩,?_⟩
  apply missing_eq fresh
  · intro y hy
    rw [agrees (hsT hy)]
    exact (orbit (hsT hy)).1
  · have fx := orbit hx
    exact mem_image.mpr ⟨f x,(mem_insert.mp fx.1).resolve_left fx.2.1.symm,
      (agrees fx.1).trans (inv hx)⟩

/-- The involution criterion is independent of an enumeration of the sites. -/
theorem reflects_iff {I : Type} [Fintype I] (D : I ↪ F) :
    Reflects D ↔ PairedSet (univ.image D) := by
  constructor
  · rintro ⟨a,b,c,valid,all⟩
    refine ⟨a,b,c,valid,?_⟩
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,ij,rel⟩ := all i
    exact ⟨D j,mem_image_of_mem D (mem_univ _),D.injective.ne ij,rel⟩
  · rintro ⟨a,b,c,valid,all⟩
    refine ⟨a,b,c,valid,?_⟩
    intro i
    obtain ⟨x,hx,ineq,rel⟩ := all (D i) (mem_image_of_mem D (mem_univ _))
    obtain ⟨j,_,rfl⟩ := mem_image.mp hx
    exact ⟨j,fun h => ineq (congrArg D h),rel⟩

/-- For every prescribed set of all but one site, all but quadratically many
completions realize the smaller dimension-three endpoint mass. -/
theorem mass_outside [Fintype F] {h : ℕ} (S : Finset F) (size : S.card=2*h+1)
    (large : 4≤h) (odd : h%2=1) :
    ∃ B : Finset F, B.card≤16*S.card^2 ∧ ∀ x∉S, x∉B →
      ∀ D : Fin (2*h+2) ↪ F, univ.image D=insert x S →
      epsMCA (F:=F) (ReedSolomon.code D 3 : Set (Fin (2*h+2) → F))
        (((h-1:ℕ):ℝ≥0)/(2*h+2:ℕ))=(h:ℝ≥0∞)/Fintype.card F := by
  classical
  obtain ⟨B,hB,blocks⟩ := completions S (by omega)
  refine ⟨B,hB,?_⟩
  intro x fresh outside D image
  have absent : ¬ Reflects D := fun r => outside (blocks x fresh (image ▸ (reflects_iff D).1 r))
  have mass := DimensionThreePairCriterion.mass (h:=h) D (by simp) large odd
  rw [ite_eq_right (fun pairs => absent (necessary D (by simp) (by omega) pairs))] at mass
  simpa only [Fintype.card_fin] using mass

/-- In particular, a small prescribed set can always be completed by one site
without a projective pairing, at every sufficiently large field order. -/
theorem exists_completion [Fintype F] (S : Finset F) (size : 4≤S.card)
    (room : S.card+16*S.card^2<Fintype.card F) :
    ∃ x∉S, ¬PairedSet (insert x S) := by
  obtain ⟨B,hB,blocks⟩ := completions S size
  have bound := card_union_le S B
  obtain ⟨x,_,free⟩ := exists_mem_notMem_of_card_lt_card
    (s:=S∪B) (t:=univ) (by rw [card_univ];omega)
  have fresh := fun hx => free (mem_union_left B hx)
  exact ⟨x,fresh,fun paired => free (mem_union_right S (blocks x fresh paired))⟩

end ProximityGap.ProjectivePairCompletions
#print axioms ProximityGap.ProjectivePairCompletions.completions

#print axioms ProximityGap.ProjectivePairCompletions.mass_outside
#print axioms ProximityGap.ProjectivePairCompletions.exists_completion
