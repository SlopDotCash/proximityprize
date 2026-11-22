/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReflectionListSampling
import ArkLib.Research.ProximityGap.Frontier.AuxiliaryReflectionRow

/-! # From a bound on transpositions to a bound on nonreflection fibers -/
namespace ProximityGap.ReflectionListSampling

open Finset TwoErrorSlice

/-- Arbitrary bounds on the number of non-dihedral transpositions supply
the pair-cap hypothesis used by list sampling. -/
theorem pairCap_of_involutions {I F : Type*} [Fintype I] [DecidableEq I] [Field F]
    (D : I ↪ F) {T : ℕ} (hT : 1≤T) (nz : ∀ i,D i≠0)
    (rigid : ∀ (p : Fin (T+1) × Fin 2 ↪ I) (a b c : F), a^2+b*c≠0 →
      (∀ i, c*D (p (i,0))*D (p (i,1))-a*(D (p (i,0))+D (p (i,1)))=b) →
      a=0 ∨ c=0 ∧ b=0) : PairCap D T := by
  classical
  intro u v uv anti t nonref
  let base : Finset I := {u,v}
  let alts := alternatives D u v t
  let S := insert base alts
  have shape {A} (h : A∈alts) := mem_alternatives_iff.mp h
  have outside {A} (h : A∈alts) {x} (hx : x∈A) : x≠v ∧ x≠u := by
    simpa only [mem_erase,mem_univ,and_true] using (mem_powersetCard.mp (shape h).1).1 hx
  have absent : base∉alts := fun h => (outside h (mem_insert_self u {v})).2 rfl
  by_contra! large
  change T < alts.card+1 at large
  have num : T+1≤Fintype.card S := by
    rw [Fintype.card_coe,show S.card=alts.card+1 from card_insert_of_notMem absent]
    omega
  have nonempty : alts.Nonempty := card_pos.mp (by omega)
  obtain ⟨A,hA⟩ := nonempty
  have nt : t≠0 := (shape hA).2 ▸ prod_ne_zero_iff.mpr (fun x hx =>
    ratio_ne_zero D (outside hA hx).2.symm (outside hA hx).1.symm)
  let a := D u-t*D v
  let b := t*(D v)^2-(D u)^2
  let c := 1-t
  have det : a^2+b*c≠0 := by
    rw [show a^2+b*c=t*(D u-D v)^2 by dsimp [a,b,c];ring]
    exact mul_ne_zero nt (pow_ne_zero _ (sub_ne_zero.mpr (D.injective.ne uv)))
  have size {A} (h : A∈S) : A.card=2 := by
    rcases mem_insert.mp h with rfl|h
    · exact card_pair uv
    · exact (mem_powersetCard.mp (shape h).1).2
  have curve {x y : I} {A : Finset I} (h : A∈S) (xy : x≠y) (eq : A={x,y}) :
      c*D x*D y-a*(D x+D y)=b := by
    rcases mem_insert.mp h with h|h
    · have baseEq : ({u,v} : Set I)={x,y} := by
        simpa only [base,Finset.coe_insert,Finset.coe_singleton] using congrArg (fun Q : Finset I => (Q : Set I)) (h.symm.trans eq)
      rcases Set.pair_eq_pair_iff.mp baseEq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> dsimp [a,b,c] <;> ring
    · have hx := outside h (eq ▸ mem_insert_self x {y})
      have hy := outside h (eq ▸ mem_insert_of_mem (mem_singleton_self y))
      have val := (shape h).2
      rw [eq,prod_pair xy,ratio,ratio,div_mul_div_comm] at val
      have cleared := (div_eq_iff (mul_ne_zero (sub_ne_zero.mpr (D.injective.ne hx.1.symm))
        (sub_ne_zero.mpr (D.injective.ne hy.1.symm)))).mp val
      dsimp [a,b,c]; linear_combination cleared
  let members : Fin (T+1) ↪ S := (Fin.castLEEmb num).trans (Fintype.equivFin S).symm.toEmbedding
  let P (i : Fin (T+1)) := (members i).val
  let f (i : Fin (T+1)) : Fin 2 ≃ (P i) :=
    (Fintype.equivFinOfCardEq ((Fintype.card_coe (P i)).trans (size (members i).property))).symm
  let node (i : Fin (T+1)) (k : Fin 2) := (f i k).val
  have ni (i) : Function.Injective (node i) := Subtype.val_injective.comp (f i).injective
  have distinct (i) : node i 0 ≠ node i 1 := (ni i).ne (by decide)
  have pair (i) : P i={node i 0,node i 1} := by
    apply (eq_of_subset_of_card_le ?_ ?_).symm
    · exact insert_subset (f i 0).property (singleton_subset_iff.mpr (f i 1).property)
    · rw [size (members i).property,card_pair (distinct i)]
  have law (i) := curve (members i).property (distinct i) (pair i)
  have coll {x y z : F} (xy : c*x*y-a*(x+y)=b) (xz : c*x*z-a*(x+z)=b) : y=z := by
    have den : c*x-a≠0 := by
      intro h
      have zero : a*x+b=0 := by linear_combination y*h-xy
      exact det (by linear_combination c*zero-a*h)
    have h : (c*x-a)*(y-z)=0 := by linear_combination xy-xz
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left den)
  have disj {i j : Fin (T+1)} (hij : i≠j) : Disjoint (P i) (P j) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hi := law i
    have hj := law j
    have si : c*D (node i 1)*D (node i 0)-a*(D (node i 1)+D (node i 0))=b := by linear_combination hi
    have sj : c*D (node j 1)*D (node j 0)-a*(D (node j 1)+D (node j 0))=b := by linear_combination hj
    rw [pair i] at hx
    rw [pair j] at hy
    simp only [mem_insert,mem_singleton] at hx hy
    apply hij
    apply members.injective
    apply Subtype.ext
    change P i=P j
    rw [pair i,pair j]
    rcases hx with rfl|rfl <;> rcases hy with eq|eq
    · rw [eq] at hi ⊢
      rw [D.injective (coll hi hj)]
    · rw [eq] at hi ⊢
      rw [D.injective (coll hi sj),pair_comm]
    · rw [eq] at si ⊢
      rw [D.injective (coll si hj),pair_comm]
    · rw [eq] at si ⊢
      rw [D.injective (coll si sj)]
  let pts : Fin (T+1) × Fin 2 ↪ I := ⟨fun x => node x.1 x.2,by
    rintro ⟨i,r⟩ ⟨j,s⟩ h
    change node i r=node j s at h
    have ix : i=j := by
      by_contra diff
      have hr : node i r∈P i := (f i r).property
      have hs : node j s∈P j := (f j s).property
      exact disjoint_left.mp (disj diff) hr (h ▸ hs)
    subst j
    exact congrArg (Prod.mk i) (ni i h)⟩
  rcases rigid pts a b c det law with h|⟨hc,hb⟩
  · exact nonref ((eq_div_iff (nz v)).mpr (sub_eq_zero.mp h).symm)
  · have tt : t=1 := (sub_eq_zero.mp hc).symm
    have sq : D u^2=D v^2 := by dsimp [b] at hb; rw [tt,one_mul] at hb; exact (sub_eq_zero.mp hb).symm
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp sq).elim (D.injective.ne uv) anti

end ProximityGap.ReflectionListSampling

#print axioms ProximityGap.ReflectionListSampling.pairCap_of_involutions
