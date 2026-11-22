/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicRationalParity

/-! # Bounding all dyadic matches when neither antipodal identity holds -/
namespace ProximityGap.DyadicRationalSites
open Finset Polynomial DyadicRationalParity
variable {K : Type*} [Field K]

/-- The numerator of the signed antipodal comparison for P/Q. -/
noncomputable def comparison (P Q : K[X]) (e : K) :=
  P.comp (-X)*Q-C e*P*(Q.comp (-X))

private theorem comparison_degree {P Q : K[X]} {d : ℕ} (p : P.natDegree≤d)
    (q : Q.natDegree≤d) (e : K) : (comparison P Q e).natDegree≤2*d := by
  have comp (R : K[X]) : (R.comp (-X)).natDegree≤R.natDegree := (natDegree_comp_le).trans (by simp)
  apply (natDegree_sub_le _ _).trans (max_le _ _)
  · exact natDegree_mul_le.trans ((Nat.add_le_add ((comp P).trans p) q).trans (by omega))
  · exact natDegree_mul_le.trans ((Nat.add_le_add ((natDegree_C_mul_le _ _).trans p) ((comp Q).trans q)).trans (by omega))

/-- Bound distinct sampled zeros by the degree of a nonzero polynomial. -/
theorem zeros {a : Type*} [Fintype a] {P : K[X]} (pn : P≠0) (x : a → K)
    (ix : Function.Injective x) (S : Finset a) (zero : ∀ i ∈ S, P.eval (x i)=0) :
    S.card≤P.natDegree := by
  by_contra! h
  apply pn
  apply eq_zero_of_degree_lt_of_eval_index_eq_zero S ix.injOn _ zero
  exact degree_le_natDegree.trans_lt (by exact_mod_cast h)

/-- When a rational function is neither even nor odd, the total number of
matched inputs on any dyadic orbit is at most twelve times its degree bound.
Output repetitions are allowed. -/
theorem bound [CharZero K] [Algebra ℚ K] [Normal ℚ K] {m d n : ℕ} (hd : 0<d) {z : K}
    (hz : IsPrimitiveRoot z (2^m)) (P Q : K[X]) (p : P.natDegree≤d) (q : Q.natDegree≤d)
    (plus : comparison P Q 1≠0) (minus : comparison P Q (-1)≠0) (A B : Fin n → ℕ)
    (ix : Function.Injective (fun i => z^(A i))) (nz : ∀ i, Q.eval (z^(A i))≠0)
    (law : ∀ i, P.eval (z^(A i))=z^(B i)*Q.eval (z^(A i))) : n≤12*d := by
  classical
  let x (i : Fin n) := z^(A i)
  let y (i : Fin n) := z^(B i)
  let bad (e : K) := univ.filter fun i => P.eval (-x i)=e*y i*Q.eval (-x i)
  have bad_bound {e : K} (nonzero : comparison P Q e≠0) : (bad e).card≤2*d := by
    apply le_trans _ (comparison_degree p q e)
    apply zeros nonzero x ix
    intro i hi
    have match' := (mem_filter.mp hi).2
    have law_i : P.eval (x i)=y i*Q.eval (x i) := law i
    simp only [comparison,eval_sub,eval_mul,eval_comp,eval_neg,eval_X,eval_C]
    rw [match',law_i]
    ring
  let S : Finset (Fin n) := univ \ (bad 1 ∪ bad (-1))
  have clean_bound : S.card≤8*d := by
    let f : Fin S.card ↪ Fin n := (Fintype.equivFinOfCardEq (α:=S)
      (Fintype.card_coe S)).symm.toEmbedding.trans (Function.Embedding.subtype _)
    have mem (i) : f i∈S := ((Fintype.equivFinOfCardEq (α:=S) (Fintype.card_coe S)).symm i).property
    exact DyadicRationalParity.bound hd hz P Q p q (A ∘ f) (B ∘ f) (ix.comp f.injective)
      (by
        intro i
        have good := (mem_sdiff.mp (mem i)).2
        have a : f i∉bad 1 := fun h => good (mem_union_left _ h)
        have b : f i∉bad (-1) := fun h => good (mem_union_right _ h)
        simp only [bad,mem_filter,mem_univ,true_and,one_mul,neg_one_mul] at a b
        exact ⟨nz _,law _,a,b⟩)
  have total := card_sdiff_add_card_eq_card (t:=univ) (s:=bad 1 ∪ bad (-1)) (subset_univ _)
  have costs := card_union_le (bad 1) (bad (-1))
  change S.card+_= _ at total
  simp only [card_univ,Fintype.card_fin] at total
  have one := bad_bound plus
  have two := bad_bound minus
  omega

end ProximityGap.DyadicRationalSites
#print axioms ProximityGap.DyadicRationalSites.bound
