/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReciprocalChartMCA

/-! # Eliminating all off-diagonal short additive relations in one chart

Ordered tuples may repeat sites. The coefficient of each simple pole is the
difference of its two multiplicities. In prime characteristic above the tuple
length, a genuine difference in multiplicity stays nonzero in the field.
-/
set_option autoImplicit false
namespace ProximityGap.ReciprocalTupleEnergy
open Finset Polynomial Lagrange
variable {F I : Type} [Field F] [DecidableEq F] [DecidableEq I]
variable {r : ℕ}

/-- Multiplicity of a site in an ordered tuple. -/
def count (a : Fin r → I) (i : I) : ℕ := (univ.filter fun j => a j = i).card

private theorem count_le (a : Fin r → I) (i : I) : count a i ≤ r := by
  simpa [count] using (card_filter_le (s:=(univ : Finset (Fin r))) (fun j => a j = i))

omit [DecidableEq F] in
private theorem sum_count (a : Fin r → I) (W : Finset I) (g : I → F) (h : ∀ j, a j ∈ W) :
    ∑ i ∈ W, (count a i : F)*g i = ∑ j, g (a j) := by
  simpa only [count,sum_const,nsmul_eq_mul] using
    (sum_fiberwise_of_maps_to' (s:=(univ : Finset (Fin r))) (t:=W) (g:=a) (fun j _ => h j) g)

private theorem count_zero (a : Fin r → I) (i : I) (h : i ∉ univ.image a) : count a i = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  exact h (mem_image.mpr ⟨j,mem_univ _,(mem_filter.mp hj).2⟩)

/-- One nontrivial ordered tuple relation excludes at most twice its length in poles. -/
theorem weighted_pair [Fintype I] [Fintype F] (x : I ↪ F) (a b : Fin r → I)
    (ne : ∃ i, (count a i : F) ≠ (count b i : F)) :
    ((univ : Finset F).filter fun t => (∀ i, t ≠ x i) ∧
      (∑ j, (t-x (a j))⁻¹) = ∑ j, (t-x (b j))⁻¹).card ≤ 2*r := by
  classical
  let W := univ.image a ∪ univ.image b
  let c (i : I) := (count a i : F)-(count b i : F)
  let P : F[X] := ∑ i ∈ W, C (c i)*nodal (W.erase i) x
  obtain ⟨i,hi⟩ := ne
  have hin : i ∈ W := by
    by_contra hh
    have h' := not_or.mp (fun h => hh (mem_union.mpr h))
    exact hi (by rw [count_zero a i h'.1,count_zero b i h'.2])
  have atsite : P.eval (x i) = c i*(nodal (W.erase i) x).eval (x i) := by
    rw [show P = _ from rfl, eval_finsetSum,sum_eq_single i]
    · simp
    · intro j hj hji
      rw [eval_mul,eval_C,eval_nodal_at_node (mem_erase.mpr ⟨Ne.symm hji,hin⟩),mul_zero]
    · exact fun h => (h hin).elim
  have hp : P ≠ 0 := by
    intro he
    rw [he,eval_zero] at atsite
    apply (mul_ne_zero (sub_ne_zero.mpr hi) _) atsite.symm
    exact eval_nodal_not_at_node fun j hj eq => (mem_erase.mp hj).1 (x.injective eq).symm
  have bound : W.card ≤ 2*r := by
    have ha : (univ.image a).card ≤ r := by simpa using card_image_le (s:=univ) (f:=a)
    have hb : (univ.image b).card ≤ r := by simpa using card_image_le (s:=univ) (f:=b)
    exact (card_union_le ..).trans (by omega)
  apply (card_le_degree_of_subset_roots (p:=P) ?_).trans
  · apply natDegree_sum_le_of_forall_le
    intro j _
    apply (natDegree_C_mul_le ..).trans
    rw [natDegree_nodal]
    exact (card_le_card (erase_subset j W)).trans bound
  · intro t ht
    obtain ⟨free,eq⟩ := (mem_filter.mp ht).2
    have term (j : I) (hj : j ∈ W) :
        (nodal (W.erase j) x).eval t = (t-x j)⁻¹*(nodal W x).eval t := by
      rw [nodal_eq_mul_nodal_erase hj,eval_mul,eval_sub,eval_X,eval_C,← mul_assoc,
        inv_mul_cancel₀ (sub_ne_zero.mpr (free j)),one_mul]
    have eqsum : ∑ j ∈ W, (c j)*(t-x j)⁻¹ = 0 := by
      simp only [c,sub_mul,sum_sub_distrib,sub_eq_zero]
      rw [sum_count a W _ (fun j => mem_union_left _ (mem_image_of_mem a (mem_univ j))),
        sum_count b W _ (fun j => mem_union_right _ (mem_image_of_mem b (mem_univ j)))]
      exact eq
    apply (mem_roots hp).mpr
    change P.eval t = 0
    simp only [P,eval_finsetSum,eval_mul,eval_C]
    calc ∑ j ∈ W, c j*(nodal (W.erase j) x).eval t
        = ∑ j ∈ W, (c j*(t-x j)⁻¹)*(nodal W x).eval t :=
          sum_congr rfl fun j hj => by rw [term j hj,mul_assoc]
       _ = 0 := by rw [← sum_mul,eqsum,zero_mul]

/-- One pole simultaneously rules out every r-term relation except those
whose coordinate multiplicities agree in the field. -/
theorem exists_chart [Fintype I] [Fintype F] (x : I ↪ F) (r : ℕ)
    (size : Fintype.card I + ((Fintype.card I)^r)^2*(2*r) < Fintype.card F) :
    ∃ t : F, (∀ i, t ≠ x i) ∧ ∀ (a b : Fin r → I),
      (∑ j, (t-x (a j))⁻¹) = ∑ j, (t-x (b j))⁻¹ ↔
      ∀ i, (count a i : F) = (count b i : F) := by
  classical
  let K := (univ : Finset ((Fin r → I) × (Fin r → I))).filter fun ab =>
    ∃ i, (count ab.1 i : F) ≠ (count ab.2 i : F)
  let bad (ab : (Fin r → I) × (Fin r → I)) := (univ : Finset F).filter fun t =>
    (∀ i, t ≠ x i) ∧ (∑ j, (t-x (ab.1 j))⁻¹) = ∑ j, (t-x (ab.2 j))⁻¹
  let E := (univ.image fun i => x i) ∪ K.biUnion bad
  have bound : (K.biUnion bad).card ≤ ((Fintype.card I)^r)^2*(2*r) := by
    calc (K.biUnion bad).card ≤ ∑ ab ∈ K, (bad ab).card := card_biUnion_le
         _ ≤ ∑ _ab ∈ K, 2*r := sum_le_sum fun ab hab => weighted_pair x _ _ (mem_filter.mp hab).2
         _ ≤ _ := by
           simp only [sum_const,nsmul_eq_mul]
           apply Nat.mul_le_mul_right
           exact (card_le_card (filter_subset ..)).trans_eq (by simp [sq])
  have cardE : E.card < Fintype.card F := (card_union_le ..).trans_lt
    ((Nat.add_le_add (card_image_le.trans_eq card_univ) bound).trans_lt size)
  obtain ⟨t,_,ht⟩ := exists_mem_notMem_of_card_lt_card (t:=univ) (by simpa using cardE)
  have free (i : I) : t ≠ x i := fun h => ht (mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,h.symm⟩))
  refine ⟨t,free,fun a b => ⟨?_,?_⟩⟩
  · intro eq i
    by_contra ne
    apply ht
    exact mem_union_right _ (mem_biUnion.mpr ⟨(a,b),mem_filter.mpr ⟨mem_univ _,i,ne⟩,
      mem_filter.mpr ⟨mem_univ _,free,eq⟩⟩)
  · intro h
    rw [← sum_count a univ (fun i => (t-x i)⁻¹) (fun _ => mem_univ _),
      ← sum_count b univ (fun i => (t-x i)⁻¹) (fun _ => mem_univ _)]
    exact sum_congr rfl fun i _ => by rw [h i]

/-- In a prime field above the tuple length, the only collisions permute the same multiset. -/
theorem prime_chart {p : ℕ} [Fact p.Prime] [Fintype I] (x : I ↪ ZMod p) (r : ℕ)
    (hr : r < p) (size : Fintype.card I + ((Fintype.card I)^r)^2*(2*r) < p) :
    ∃ t : ZMod p, (∀ i, t ≠ x i) ∧ ∀ (a b : Fin r → I),
      (∑ j, (t-x (a j))⁻¹) = ∑ j, (t-x (b j))⁻¹ ↔ ∀ i, count a i = count b i := by
  obtain ⟨t,ht,he⟩ := exists_chart x r (by simpa using size)
  refine ⟨t,ht,fun a b => (he a b).trans ⟨?_,?_⟩⟩
  · intro h i
    have := congrArg ZMod.val (h i)
    simpa [ZMod.val_natCast_of_lt ((count_le a i).trans_lt hr),
      ZMod.val_natCast_of_lt ((count_le b i).trans_lt hr)] using this
  · intro h i
    exact congrArg (fun n : ℕ => (n : ZMod p)) (h i)

/-- Equal multiplicities give a permutation of the tuple positions. -/
theorem perm_of_count_eq (a b : Fin r → I) (h : ∀ i, count a i = count b i) :
    ∃ σ : Equiv.Perm (Fin r), ∀ j, a (σ j) = b j := by
  classical
  let e (i : I) : {j // b j = i} ≃ {j // a j = i} := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_subtype, count] using (h i).symm)
  let σ := (Equiv.sigmaFiberEquiv b).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv a))
  exact ⟨σ,fun j => (e (b j) ⟨j,rfl⟩).property⟩

end ProximityGap.ReciprocalTupleEnergy
#print axioms ProximityGap.ReciprocalTupleEnergy.exists_chart
#print axioms ProximityGap.ReciprocalTupleEnergy.prime_chart
