/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SixSplitListWitness

/-! # Five saturated Reed–Solomon messages with exact-sized agreement witnesses

The pair exponents of five reciprocal affine functions are distinct on a sixteenth-root
domain. A separate reserve suffices for all five exact agreement supports.
-/
namespace ProximityGap.FiveCroppedSplitPencil

open Finset Polynomial
open SixSplitListWitness (sitesOn sitesOn_card)
variable {I F : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
  [Nonempty I]

private def exponent : Fin 5 → ℕ := ![0,1,2,4,7]
private def sig (i j : Fin 5) : Fin 16 :=
  ⟨exponent i+exponent j,(by decide : ∀ i j : Fin 5, exponent i+exponent j < 16) i j⟩
private def unused : Finset (Fin 16) := {0,10,12,13,14,15}
private def incident : Fin 5 → Finset (Fin 16) :=
  ![{1,2,4,7}, {1,3,5,8}, {2,3,6,9}, {4,5,6,11}, {7,8,9,11}]
private def owner : Fin 16 → Fin 5 := ![0,0,0,1,0,1,2,0,1,2,0,3,0,0,0,0]

omit [Fintype F] [DecidableEq F] in
private theorem head_eq {z : F} (hz : IsPrimitiveRoot z 16) {j l : Fin 5} (hne : j ≠ l)
    (y : F) : z^(exponent j) + (z^(exponent j))⁻¹*y =
      z^(exponent l) + (z^(exponent l))⁻¹*y ↔ y=z^(sig j l).val := by
  have hne' : z^(exponent j) ≠ z^(exponent l) := by
    intro h
    have hlt := (by decide : ∀ i : Fin 5, exponent i < 16)
    exact hne ((by decide : Function.Injective exponent) (hz.pow_inj (hlt j) (hlt l) h))
  have hn := hz.ne_zero (by decide : 16 ≠ 0)
  have hj := pow_ne_zero (exponent j) hn
  have hl := pow_ne_zero (exponent l) hn
  change _ ↔ y=z^(exponent j + exponent l)
  rw [pow_add]
  constructor
  · intro h
    field_simp at h
    apply mul_left_cancel₀ (sub_ne_zero.mpr hne')
    linear_combination -h
  · rintro rfl
    field_simp
    ring

/-- The five exact chosen supports jointly preserve every saturated pair intersection.
This holds throughout the entire agreement interval from 5d−1 through 6d−1. -/
theorem smooth (D : I ↪ F) [ReedSolomon.Smooth D] {d t : ℕ} (hd : 0 < d)
    (hn : Fintype.card I = d*16) (ht₀ : 5*d-1 ≤ t) (ht₁ : t ≤ 6*d-1) :
    ∃ (w : Fin 5 ↪ (I → F)) (y : I → F) (S : Fin 5 → Finset I),
      (∀ j, w j ∈ (ReedSolomon.code D (2*d) : Set (I → F))) ∧
      (∀ j, (S j).card = t) ∧ (∀ j i, i ∈ S j → y i = w j i) ∧
      ∀ j l, j ≠ l → (S j ∩ S l).card = 2*d-1 := by
  classical
  obtain ⟨π,Y,z,hf,hy,hz,hY⟩ := SixSplitListWitness.exists_coordinates D hd hn
  let pool := sitesOn π unused
  have hpool : pool.card = 6*d := (sitesOn_card hf unused).trans (by rfl)
  obtain ⟨common, hcommon, hc⟩ := Finset.exists_subset_card_eq
    (show d-1 ≤ pool.card by rw [hpool]; omega)
  let spare := pool \ common
  have hspare : spare.card = 5*d+1 := by
    rw [Finset.card_sdiff_of_subset hcommon, hpool, hc]
    omega
  let P := Lagrange.nodal common D
  have hP (i : I) : P.eval (D i) = 0 ↔ i ∈ common := by
    simp [P, Lagrange.eval_nodal, Finset.prod_eq_zero_iff, sub_eq_zero, D.injective.eq_iff]
  let b (j : Fin 5) := z^(exponent j)
  let message (j : Fin 5) : F[X] := P*(C (b j)+C (b j)⁻¹*Y)
  let w (j : Fin 5) (i : I) : F := (message j).eval (D i)
  have hdeg (j : Fin 5) : (message j).natDegree < 2*d := by
    have ha : (C (b j)⁻¹*Y).natDegree ≤ d := (natDegree_C_mul_le _ _).trans hy
    have hb : (C (b j)+C (b j)⁻¹*Y).natDegree ≤ d :=
      (natDegree_add_le _ _).trans (max_le (by simp) ha)
    have hp : P.natDegree = d-1 := Lagrange.natDegree_nodal.trans hc
    exact (natDegree_mul_le.trans (Nat.add_le_add (Nat.le_of_eq hp) hb)).trans_lt (by omega)
  have heq (j l : Fin 5) (hne : j ≠ l) (i : I) :
      w j i = w l i ↔ i ∈ common ∨ π i = sig j l := by
    simp only [w,message,b,eval_mul,eval_add,eval_C,mul_eq_mul_left_iff,hY,
      head_eq hz hne,hP]
    rw [show (z^(π i).val = z^(sig j l).val) ↔ π i = sig j l from
      ⟨fun h => Fin.ext (hz.pow_inj (π i).isLt (sig j l).isLt h), fun h => by rw [h]⟩]
    tauto
  have hdis (j : Fin 5) : Disjoint pool (sitesOn π (incident j)) := by
    apply disjoint_left.mpr
    intro i hi hj
    exact (by decide : ∀ j : Fin 5, ∀ b ∈ unused, b ∉ incident j) j (π i)
      (mem_filter.mp hi).2 (mem_filter.mp hj).2
  let B (j : Fin 5) := common ∪ sitesOn π (incident j)
  have hB (j : Fin 5) : (B j).card = 5*d-1 := by
    have hcard := (by decide : ∀ j : Fin 5, (incident j).card = 4) j
    rw [card_union_of_disjoint ((hdis j).mono_left hcommon), hc, sitesOn_card hf, hcard]
    omega
  let g := t-(5*d-1)
  obtain ⟨y, outside, extra⟩ := ReciprocalFiberLists.split_fiber spare (univ : Finset (Fin 5))
    g (fun i => w (owner (π i)) i) w (by rw [hspare]; change 5*g ≤ _; dsimp [g]; omega)
  have onB (j : Fin 5) {i : I} (hi : i ∈ B j) : y i = w j i := by
    rcases mem_union.mp hi with h|h
    · rw [outside i (fun h' => (mem_sdiff.mp h').2 h)]
      simp only [w,message,eval_mul,(hP i).2 h,zero_mul]
    rw [outside i (fun h' => disjoint_left.mp (hdis j) (mem_sdiff.mp h').1 h)]
    rcases (by decide : ∀ j : Fin 5, ∀ a ∈ incident j,
      owner a = j ∨ a = sig (owner a) j) j (π i) (mem_filter.mp h).2 with he|he
    · rw [he]
    by_cases he' : owner (π i) = j
    · rw [he']
    exact (heq _ _ he' _).2 (Or.inr he)
  choose X hx hX using fun j : Fin 5 => Finset.exists_subset_card_eq (extra j (mem_univ j))
  let S j := B j ∪ X j
  have hs (j : Fin 5) : (S j).card = t := by
    change (B j ∪ X j).card = _
    rw [card_union_of_disjoint, hB, hX]
    · dsimp [g]; omega
    apply disjoint_left.mpr
    intro i hi hi'
    have hs := mem_sdiff.mp (mem_filter.mp (hx j hi')).1
    exact (mem_union.mp hi).elim hs.2 (fun h => disjoint_left.mp (hdis j) hs.1 h)
  have hits (j : Fin 5) (i : I) (hi : i ∈ S j) : y i = w j i :=
    (mem_union.mp hi).elim (onB j) (fun h => (mem_filter.mp (hx j h)).2)
  have pair (j l : Fin 5) (hne : j ≠ l) : S j ∩ S l =
      common ∪ (univ.filter fun i => π i = sig j l) := by
    ext i
    simp only [mem_inter,mem_union,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨a,b⟩
      exact (heq j l hne _).mp ((hits j i a).symm.trans (hits l i b))
    · rintro (h|h)
      · exact ⟨mem_union_left _ (mem_union_left _ h),mem_union_left _ (mem_union_left _ h)⟩
      have ht := (by decide : ∀ j l : Fin 5, j ≠ l → sig j l ∈ incident j ∧ sig j l ∈ incident l)
        j l hne
      exact ⟨mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h ▸ ht.1⟩)),
        mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h ▸ ht.2⟩))⟩
  have hin : Function.Injective w := by
    intro j l he
    by_contra hne
    let a : Fin 16 := if sig j l = 1 then 2 else 1
    obtain ⟨i,hi⟩ := card_pos.mp (hd.trans_eq (hf a).symm)
    have hlabel := (mem_filter.mp hi).2
    rcases (heq j l hne i).mp (congrFun he i) with h|h
    · have hi' : π i ∈ unused := (mem_filter.mp (hcommon h)).2
      rw [hlabel] at hi'
      dsimp [a] at hi'
      split at hi'
      · exact (by decide : (2 : Fin 16) ∉ unused) hi'
      · exact (by decide : (1 : Fin 16) ∉ unused) hi'
    · rw [hlabel] at h
      dsimp [a] at h
      split at h <;> omega
  refine ⟨⟨w,hin⟩,y,S,fun j => ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval _
    (hdeg j) (fun _ => rfl),hs,hits,fun j l hne => ?_⟩
  rw [pair j l hne,card_union_of_disjoint,hc,hf]
  · omega
  apply disjoint_left.mpr
  intro i hi hj
  have h := (by decide : ∀ j l : Fin 5, j ≠ l → sig j l ∉ unused) j l hne
  exact h ((mem_filter.mp hj).2 ▸ (mem_filter.mp (hcommon hi)).2)

/-- In particular cropping at the first production agreement count below Johnson retains a
complete five-clique on all smooth domains. -/
theorem production (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 1073741824) :
    ∃ (w : Fin 5 ↪ (I → F)) (y : I → F) (S : Fin 5 → Finset I),
      (∀ j, w j ∈ (ReedSolomon.code D 134217728 : Set (I → F))) ∧
      (∀ j, (S j).card = 379625061) ∧ (∀ j i, i ∈ S j → y i = w j i) ∧
      ∀ j l, j ≠ l → (S j ∩ S l).card = 134217727 :=
  smooth D (d := 67108864) (by decide) hn (by decide) (by decide)

#print axioms smooth
#print axioms production

end ProximityGap.FiveCroppedSplitPencil
