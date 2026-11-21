/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! # A finite family with bounded pairwise coordinate coincidences -/

set_option autoImplicit false
open Finset
namespace ProximityGap.FiniteFingerprintCount
variable {A B Z : Type*} [DecidableEq A] [DecidableEq B] [Fintype Z]

private theorem fiber_cauchy (P : Finset A) (v : A → B) :
    P.card^2 ≤ (P.image v).card*((P ×ˢ P).filter (fun h => v h.1=v h.2)).card := by
  classical
  let img := P.image v
  have total : ∑ b ∈ img, (P.filter fun a => v a=b).card = P.card :=
    (card_eq_sum_card_fiberwise fun a ha => mem_image_of_mem _ ha).symm
  have sq : ((P ×ˢ P).filter (fun h => v h.1=v h.2)).card =
      ∑ b ∈ img, (P.filter fun a => v a=b).card^2 := by
    have eq : (P ×ˢ P).filter (fun h => v h.1=v h.2) = img.biUnion
        (fun b => (P.filter fun a => v a=b) ×ˢ (P.filter fun a => v a=b)) := by
      ext h
      simp only [img,mem_filter,mem_product,mem_biUnion,mem_image]
      constructor
      · rintro ⟨⟨h₁,h₂⟩,he⟩
        exact ⟨v h.1,⟨h.1,h₁,rfl⟩,⟨h₁,rfl⟩,h₂,he.symm⟩
      · rintro ⟨b,_,⟨h₁,he₁⟩,h₂,he₂⟩
        exact ⟨⟨h₁,h₂⟩,he₁.trans he₂.symm⟩
    rw [eq,card_biUnion (fun b _ c _ hbc => by
      apply disjoint_left.mpr
      intro p hp hq
      exact hbc ((mem_filter.mp (mem_product.mp hp).1).2.symm.trans
        (mem_filter.mp (mem_product.mp hq).1).2))]
    simp [pow_two]
  rw [sq,← total]
  simpa using sum_mul_sq_le_sq_mul_sq (R:=ℕ) img 1 (fun b => (P.filter fun a => v a=b).card)

/-- At one coordinate there are at least |P||Z|/(|Z|+(|P|-1)d)
distinct values when each pair coincides in at most d coordinates. -/
theorem exists_large_image [Nonempty Z] (P : Finset A) (V : Z → A → B) (d : ℕ)
    (hpair : ∀ a ∈ P, ∀ b ∈ P, a≠b → (univ.filter fun z => V z a=V z b).card≤d) :
    ∃ z : Z, P.card*Fintype.card Z ≤ (P.image (V z)).card*(Fintype.card Z+(P.card-1)*d) := by
  classical
  let cnt := fun z : Z => ((P ×ˢ P).filter (fun h => V z h.1=V z h.2)).card
  let N := Fintype.card Z
  have hN : 0<N := Fintype.card_pos
  rcases Nat.eq_zero_or_pos P.card with hz | hpos
  · exact ⟨Classical.choice inferInstance,by simp [hz]⟩
  have htotal : ∑ z, cnt z ≤ P.card*(N+(P.card-1)*d) := by
    have sw : ∑ z, cnt z = ∑ h ∈ P ×ˢ P, (univ.filter fun z => V z h.1=V z h.2).card := by
      simp only [cnt,card_filter]; rw [sum_comm]
    rw [sw,← diag_union_offDiag (s:=P),sum_union (disjoint_left.mpr (fun p hp hq =>
      (mem_offDiag.mp hq).2.2 (mem_diag.mp hp).2))]
    have hd : ∑ h ∈ P.diag, (univ.filter fun z => V z h.1=V z h.2).card = P.card*N := by
      calc
        _ = ∑ _ ∈ P.diag, N := sum_congr rfl fun p hp => by simp [N,(mem_diag.mp hp).2]
        _ = _ := by simp
    rw [hd,Nat.mul_add]
    apply Nat.add_le_add_left
    calc
      _ ≤ ∑ _ ∈ P.offDiag, d := sum_le_sum fun p hp =>
        hpair p.1 (mem_offDiag.mp hp).1 p.2 (mem_offDiag.mp hp).2.1 (mem_offDiag.mp hp).2.2
      _ = _ := by simp only [sum_const,smul_eq_mul,offDiag_card];rw [←Nat.mul_assoc,Nat.mul_sub,Nat.mul_one]
  obtain ⟨z,hz⟩ : ∃ z, N*cnt z ≤ P.card*(N+(P.card-1)*d) := by
    by_contra! h
    have strict := sum_lt_sum_of_nonempty (univ_nonempty (α:=Z)) (fun z _ => h z)
    rw [sum_const,card_univ,← mul_sum,smul_eq_mul] at strict
    exact (Nat.mul_le_mul_left N htotal).not_gt strict
  refine ⟨z,?_⟩
  apply Nat.le_of_mul_le_mul_left (c:=P.card) _ hpos
  calc
    P.card*(P.card*N) = P.card^2*N := by ring
    _ ≤ ((P.image (V z)).card*cnt z)*N := Nat.mul_le_mul_right _ (fiber_cauchy P (V z))
    _ = (P.image (V z)).card*(N*cnt z) := by ring
    _ ≤ _ := (Nat.mul_le_mul_left (P.image (V z)).card hz).trans_eq (by ring)

#print axioms exists_large_image
end ProximityGap.FiniteFingerprintCount
