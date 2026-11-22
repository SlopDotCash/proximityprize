/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReflectionRowTransfer

/-! # Four transpositions determine a dihedral involution on a rigid multiplicative orbit -/

namespace ProximityGap.FourInvolutionPairs

open Finset TwoErrorSlice

/-- For a trace-zero projective map, every transposition on the same curve
gives the same product of the two ratios based at a fixed transposition. -/
private theorem common_product {K : Type*} [Field K] {a b c u v x y : K}
    (det : a^2+b*c ≠ 0) (base : c*u*v-a*(u+v)=b) (other : c*x*y-a*(x+y)=b)
    (hx : v≠x) (hy : v≠y) :
    (u-x)/(v-x)*((u-y)/(v-y))=(c*u-a)/(c*v-a) := by
  have den : c*v-a ≠ 0 := by
    intro zero
    have cb : a*v+b=0 := by linear_combination u*zero-base
    exact det (by linear_combination c*cb-a*zero)
  rw [div_mul_div_comm,div_eq_div_iff (mul_ne_zero (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy)) den]
  linear_combination (u-v)*(base-other)

/-- Suppose three representations on a nonantipodal row force the reflection
product. A nonidentity projective involution exchanging four disjoint pairs
then has either zero diagonal or zero off-diagonals in trace-zero coordinates.
These give maps x ↦ b/(cx) and x ↦ −x respectively. -/
theorem classify {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
    (D : I ↪ K) (nz : ∀ i, D i≠0)
    (rigid : ∀ u v : I, u≠v → D u ≠ -D v → ∀ t : K,
      3 ≤ (alternatives D u v t).card → t=D u/D v)
    (points : Fin 4 × Fin 2 ↪ I) (a b c : K) (det : a^2+b*c≠0)
    (law : ∀ i : Fin 4, c*D (points (i,0))*D (points (i,1)) -
      a*(D (points (i,0))+D (points (i,1)))=b) : a=0 ∨ c=0 ∧ b=0 := by
  classical
  let left (i : Fin 4) := points (i,0)
  let right (i : Fin 4) := points (i,1)
  let pair (i : Fin 4) : Finset I := {left i,right i}
  have sep {i j : Fin 4} {r s : Fin 2} (h : i≠j) :
      points (i,r) ≠ points (j,s) := fun h' => h (congrArg Prod.fst (points.injective h'))
  have ends (i : Fin 4) : left i≠right i := fun h =>
    (by decide : (0:Fin 2)≠1) (congrArg Prod.snd (points.injective h))
  have inj : Function.Injective pair := by
    intro i j he
    by_contra ne
    have mem : left i ∈ pair j := he ▸ mem_insert_self ..
    simp only [pair,mem_insert,mem_singleton] at mem
    exact mem.elim (sep ne) (sep ne)
  by_cases allAnti : ∀ i, D (left i) = -D (right i)
  · right
    have eqn (i : Fin 4) : -(c*(D (right i))^2)=b := by
      have hi := law i
      change c*D (left i)*D (right i)-a*(D (left i)+D (right i))=b at hi
      rw [allAnti] at hi
      linear_combination hi
    have ne : D (right 0)^2≠D (right 1)^2 := by
      intro he
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
      · exact sep (by decide : (0:Fin 4)≠1) (D.injective h)
      · exact sep (by decide : (0:Fin 4)≠1) (D.injective (h.trans (allAnti 1).symm))
    have hz : c*(D (right 0)^2-D (right 1)^2)=0 := by linear_combination eqn 1-eqn 0
    have hc := (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr ne)
    exact ⟨hc,by simpa [hc] using (eqn 0).symm⟩
  · obtain ⟨i,hi⟩ := not_forall.mp allAnti
    let u := left i
    let v := right i
    let t := (c*D u-a)/(c*D v-a)
    have inc : ((univ.erase i).image pair) ⊆ alternatives D u v t := by
      intro A hA
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hA
      have ne := (mem_erase.mp hj).1
      refine mem_alternatives_iff.mpr ⟨mem_powersetCard.mpr ⟨?_,card_pair (ends j)⟩,?_⟩
      · intro x hx
        simp only [pair,mem_insert,mem_singleton] at hx
        simp only [mem_erase,mem_univ,and_true]
        rcases hx with rfl|rfl <;> exact ⟨sep ne,sep ne⟩
      · rw [show pair j={left j,right j} by rfl,prod_pair (ends j)]
        exact common_product det (law i) (law j) (D.injective.ne (sep ne.symm))
          (D.injective.ne (sep ne.symm))
    have size : ((univ.erase i).image pair).card=3 := by
      rw [card_image_of_injective _ inj,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin]
    have ht := rigid u v (ends i) hi t (size ▸ card_le_card inc)
    have den : c*D v-a≠0 := by
      intro zero
      have h : a*D v+b=0 := by linear_combination D u*zero-law i
      exact det (by linear_combination c*h-a*zero)
    have h := (div_eq_div_iff den (nz v)).mp ht
    have hz : a*(D u-D v)=0 := by linear_combination h
    exact Or.inl ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr (D.injective.ne (ends i))))

end ProximityGap.FourInvolutionPairs

#print axioms ProximityGap.FourInvolutionPairs.classify
