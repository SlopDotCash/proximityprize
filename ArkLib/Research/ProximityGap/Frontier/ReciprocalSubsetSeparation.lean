/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Distinct subset sums in a reciprocal coordinate chart

For any finite evaluation domain, a single pole outside the domain can
separate all sums of r distinct transformed sites when the field is larger
than the explicit union bound. Distinct site sets give different logarithmic
derivatives, even in positive characteristic, since the poles are simple.
-/

set_option autoImplicit false
namespace ProximityGap.ReciprocalSubsetSeparation
open Polynomial Finset Lagrange
variable {I F : Type*} [Field F] [DecidableEq F] [DecidableEq I]

omit [DecidableEq F] in
private theorem derivative_sum (S : Finset I) (v : I → F) (z : F)
    (hz : ∀ i ∈ S, z ≠ v i) :
    (nodal S v).derivative.eval z = (∑ i ∈ S, (z-v i)⁻¹)*(nodal S v).eval z := by
  rw [derivative_nodal,eval_finsetSum,Finset.sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [nodal_eq_mul_nodal_erase hi,eval_mul,eval_sub,eval_X,eval_C]
  rw [← mul_assoc,inv_mul_cancel₀ (sub_ne_zero.mpr (hz i hi)),one_mul]

omit [DecidableEq F] in
/-- Swapping two distinct supports makes a nonzero cleared numerator. -/
private theorem numerator_ne (v : I ↪ F) (S T : Finset I) (h : ¬ S ⊆ T) :
    (nodal S v).derivative*nodal T v - (nodal T v).derivative*nodal S v ≠ 0 := by
  obtain ⟨i,hi,hout⟩ := not_subset.mp h
  intro zero
  have hz := congrArg (eval (v i)) zero
  rw [eval_sub,eval_mul,eval_mul,eval_nodal_at_node hi,mul_zero,sub_zero,eval_zero,
    eval_nodal_derivative_eval_node_eq hi] at hz
  apply (mul_ne_zero _ _) hz
  · exact eval_nodal_not_at_node fun j hj he => (mem_erase.mp hj).1 (v.injective he).symm
  · exact eval_nodal_not_at_node fun j hj he => hout (v.injective he ▸ hj)

/-- Number of poles outside the domain causing one prescribed pair of
distinct equal-size subsets to have the same reciprocal sum. -/
theorem pair_collisions [Fintype F] [Fintype I] (v : I ↪ F) (S T : Finset I)
    (hne : S ≠ T) (hc : S.card = T.card) :
    ((univ : Finset F).filter fun z => (∀ i, z ≠ v i) ∧
       ∑ i ∈ S, (z-v i)⁻¹ = ∑ i ∈ T, (z-v i)⁻¹).card ≤ 2*S.card := by
  classical
  let P := (nodal S v).derivative*nodal T v - (nodal T v).derivative*nodal S v
  have hp : P ≠ 0 := numerator_ne v S T (fun h => hne (eq_of_subset_of_card_le h hc.ge))
  apply (card_le_degree_of_subset_roots (p:=P) ?_).trans
  · apply (natDegree_sub_le ..).trans (max_le _ _)
    · exact natDegree_mul_le.trans (by
        have h := natDegree_derivative_le (p:=nodal S v)
        rw [natDegree_nodal] at h ⊢
        omega)
    · exact natDegree_mul_le.trans (by
        have h := natDegree_derivative_le (p:=nodal T v)
        rw [natDegree_nodal] at h ⊢
        omega)
  · intro z hz
    obtain ⟨ha,eq⟩ := (mem_filter.mp hz).2
    apply (mem_roots hp).mpr
    simp only [P,IsRoot,eval_sub,eval_mul,derivative_sum _ _ z (fun i _ => ha i),eq]
    ring

/-- One evaluation chart simultaneously separates all size-r subset sums. -/
theorem exists_chart [Fintype F] [Fintype I] (v : I ↪ F) (r : ℕ)
    (size : Fintype.card I + (Fintype.card I).choose r ^ 2 * (2*r) < Fintype.card F) :
    ∃ z : F, (∀ i, z ≠ v i) ∧
      Set.InjOn (fun S : Finset I => ∑ i ∈ S, (z-v i)⁻¹)
        ((univ : Finset I).powersetCard r : Set (Finset I)) := by
  classical
  let K := (univ : Finset I).powersetCard r
  let bad (st : Finset I × Finset I) := (univ : Finset F).filter fun z =>
    (∀ i, z ≠ v i) ∧ (∑ i ∈ st.1, (z-v i)⁻¹) = ∑ i ∈ st.2, (z-v i)⁻¹
  let E := (univ.image fun i => v i) ∪ K.offDiag.biUnion bad
  have count (st : Finset I × Finset I) (hst : st ∈ K.offDiag) : (bad st).card ≤ 2*r := by
    obtain ⟨hS,hT,hne⟩ := mem_offDiag.mp hst
    have hs := (mem_powersetCard.mp hS).2
    have ht := (mem_powersetCard.mp hT).2
    exact (pair_collisions v _ _ hne (hs.trans ht.symm)).trans_eq (by rw [hs])
  have ecard : E.card < Fintype.card F := by
    apply lt_of_le_of_lt (card_union_le ..) (lt_of_le_of_lt ?_ size)
    apply Nat.add_le_add
    · exact card_image_le.trans_eq card_univ
    · calc (K.offDiag.biUnion bad).card ≤ ∑ st ∈ K.offDiag, (bad st).card := card_biUnion_le
           _ ≤ ∑ _st ∈ K.offDiag, 2*r := sum_le_sum count
           _ ≤ _ := by
             simp only [sum_const,nsmul_eq_mul,offDiag_card,K,card_powersetCard,card_univ]
             gcongr
             rw [sq]
             exact Nat.sub_le ..
  obtain ⟨z,_,hz⟩ := exists_mem_notMem_of_card_lt_card (t:=univ) (by simpa using ecard)
  have free (i : I) : z ≠ v i := fun hh => hz (mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,hh.symm⟩))
  refine ⟨z,free,?_⟩
  intro S hS T hT eq
  by_contra hne
  apply hz
  exact mem_union_right _ (mem_biUnion.mpr ⟨(S,T),mem_offDiag.mpr ⟨hS,hT,hne⟩,
    mem_filter.mpr ⟨mem_univ _,free,eq⟩⟩)

private theorem coarse_size (n r : ℕ) :
    n + n.choose r ^ 2 * (2*r) ≤ n + (n^r)^2 * (2*r) := by
  gcongr
  exact Nat.choose_le_pow ..

/-- The order-two and order-four field floors for length 2³⁰, using the
coarser bound n^r on the number of supports. -/
theorem production_sizes :
    let n : ℕ := 2^30
    n + n.choose 2 ^ 2 * (2*2) < 2^158 ∧ n + n.choose 4 ^ 2 * (2*4) < 2^245 :=
  ⟨lt_of_le_of_lt (coarse_size (2^30) 2) (by decide),
   lt_of_le_of_lt (coarse_size (2^30) 4) (by decide)⟩

end ProximityGap.ReciprocalSubsetSeparation
#print axioms ProximityGap.ReciprocalSubsetSeparation.pair_collisions
#print axioms ProximityGap.ReciprocalSubsetSeparation.exists_chart

#print axioms ProximityGap.ReciprocalSubsetSeparation.production_sizes
