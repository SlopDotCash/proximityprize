/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # A pairwise support packing at the quarter-rate Johnson successor -/

namespace ProximityGap.QuarterSupportPackingBarrier

open Finset Matrix
open scoped BigOperators

/-- Scalars for the binary hyperplanes that index the supports. -/
abbrev Bit := ZMod 2

variable {I : Type} [Fintype I] [DecidableEq I]

private def level (a : I → Bit) (u : Bit) : Finset (I → Bit) :=
  univ.filter fun x => a ⬝ᵥ x = u

private theorem level_mem (a x : I → Bit) (u : Bit) : x ∈ level a u ↔ a ⬝ᵥ x = u := by
  simp [level]

private theorem uniform {X Y : Type} [AddGroup X] [Fintype X] [AddGroup Y] [Fintype Y]
    [DecidableEq Y] (f : X →+ Y) (hf : Function.Surjective f) (b : Y) :
    (univ.filter fun x => f x = b).card * Fintype.card Y = Fintype.card X := by
  have eqs (y : Y) := AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf b)
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset X)) (t := (univ : Finset Y))
    (f := f) (fun _ _ => mem_univ _)
  simpa only [card_univ, eqs, sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] using h.symm


private theorem weight {a : I → Bit} (ha : a ≠ 0) (u : Bit) :
    (level a u).card * 2 = Fintype.card (I → Bit) := by
  let f : (I → Bit) →+ Bit :=
    { toFun := fun x => a ⬝ᵥ x
      map_zero' := dotProduct_zero _
      map_add' := dotProduct_add _ }
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := Function.ne_iff.mp ha
  have hai : a i = 1 := by
    have hz : ∀ b : Bit, b ≠ 0 → b = 1 := by decide
    exact hz _ hi
  have sur (b : Bit) : ∃ x, f x = b := by
    refine ⟨Pi.single i b, ?_⟩
    change a ⬝ᵥ Pi.single i b = b
    simp [dotProduct_single, hai]
  simpa only [level, f, ZMod.card, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using uniform f sur u

private theorem crossing {a b : I → Bit} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (u v : Bit) : (level a u ∩ level b v).card * 4 = Fintype.card (I → Bit) := by
  let M : Matrix (Fin 2) I Bit := ![a,b]
  have li : LinearIndependent Bit M.row := by
    rw [linearIndependent_fin2]
    change b ≠ 0 ∧ ∀ c : Bit, c • b ≠ a
    refine ⟨hb, fun c => ?_⟩
    have hc : c = 0 ∨ c = 1 := (by decide : ∀ c : Bit, c = 0 ∨ c = 1) c
    rcases hc with rfl | rfl <;> simp [ha.symm, hab.symm]
  have h := uniform M.mulVecLin.toAddMonoidHom li.mulVec_surjective ![u,v]
  have he : level a u ∩ level b v = univ.filter (fun x => M.mulVec x = ![u,v]) := by
    ext x
    simp only [mem_inter, level_mem, mem_filter, mem_univ, true_and]
    constructor
    · intro h
      funext i
      fin_cases i <;> first | exact h.1 | exact h.2
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
  rw [he]
  convert h using 1
  simp [ZMod.card]
  congr 2



private theorem lost {X : Type} [DecidableEq X] {A B P Q : Finset X}
    (hA : P ⊆ A) (hB : Q ⊆ B) {x : X} (hx : x ∈ A ∩ B) (hlost : x ∉ P ∩ Q) :
    (P ∩ Q).card < (A ∩ B).card := by
  apply card_lt_card
  exact (inter_subset_inter hA hB).ssubset_of_ne (fun h => hlost (h ▸ hx))

/-- A binary vector space with 4h sites supports 4h+1 blocks of size 2h−2
whose pairwise intersections have at most h−1 sites. -/
theorem packing {h : ℕ} (hh : 4 ≤ h) (hn : Fintype.card (I → Bit) = 4 * h) :
    ∃ S : Fin (4 * h + 1) → Finset (I → Bit), (∀ i, (S i).card = 2 * h - 2) ∧
      Pairwise fun i j => (S i ∩ S j).card ≤ h - 1 := by
  classical
  let J := {a : I → Bit // a ≠ 0}
  have hJ : Fintype.card J = 4 * h - 1 := by
    change Fintype.card {a : I → Bit // ¬ a = 0} = _
    rw [Fintype.card_subtype_compl, hn]
    simp
  have : Nontrivial J := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨b,c,hbc⟩ := exists_pair_ne J
  let v : Bool → J := fun j => if j then c else b
  have vinj : Function.Injective v := by
    intro i j he
    cases i <;> cases j <;> simp_all [v]
  let H (a : J) := level a.val 0
  let C (j : Bool) := level (v j).val 1
  have hw (a : J) (z : Bit) : (level a.val z).card = 2 * h := by
    have e := weight a.property z
    omega
  have hc {a b : J} (hab : a ≠ b) (z z' : Bit) : (level a.val z ∩ level b.val z').card = h := by
    have e := crossing a.property b.property (fun he => hab (Subtype.ext he)) z z'
    omega
  have zeroH (a : J) : 0 ∈ H a := by simp [H, level_mem]
  have zeroC (j : Bool) : (0 : I → Bit) ∉ C j := by simp [C, level_mem]
  have meet {a : J} {j : Bool} (hne : a ≠ v j) : ((H a) ∩ C j).Nonempty := by
    apply card_pos.mp
    rw [hc hne 0 1]
    omega
  have pick (a : J) : ∃ w ∈ H a, w ≠ 0 ∧ ∀ j, a ≠ v j → w ∈ C j := by
    by_cases hb : a = v false
    · have ht : a ≠ v true := hb ▸ fun e => Bool.false_ne_true (vinj e)
      obtain ⟨w, hw⟩ := meet ht
      obtain ⟨hwH, hwC⟩ := mem_inter.mp hw
      exact ⟨w, hwH, fun e => zeroC true (e ▸ hwC), fun j hj => by cases j <;> aesop⟩
    by_cases ht : a = v true
    · obtain ⟨w, hw'⟩ := meet hb
      obtain ⟨hwH, hwC⟩ := mem_inter.mp hw'
      exact ⟨w, hwH, fun e => zeroC false (e ▸ hwC), fun j hj => by cases j <;> aesop⟩
    have sub (j) : H a ∩ C j ⊆ (H a).erase 0 := by
      intro x hx
      obtain ⟨hxH,hxC⟩ := mem_inter.mp hx
      exact mem_erase.mpr ⟨fun e => zeroC j (e ▸ hxC),hxH⟩
    have lt : ((H a).erase 0).card < (H a ∩ C false).card + (H a ∩ C true).card := by
      rw [card_erase_of_mem (zeroH a), hw a 0, hc hb 0 1, hc ht 0 1]
      omega
    obtain ⟨w, hw'⟩ := inter_nonempty_of_card_lt_card_add_card (sub false) (sub true) lt
    obtain ⟨hf,ht'⟩ := mem_inter.mp hw'
    obtain ⟨hwH,hwf⟩ := mem_inter.mp hf
    exact ⟨w, hwH, fun e => zeroC false (e ▸ hwf), fun j _ => by
      cases j <;> first | exact hwf | exact (mem_inter.mp ht').2⟩
  choose w wH wn wC using pick
  let A (a : J) := ((H a).erase 0).erase (w a)
  have hAsub (a : J) : A a ⊆ H a := (erase_subset _ _).trans (erase_subset _ _)
  have hA (a : J) : (A a).card = 2 * h - 2 := by
    rw [show (A a).card = _ from card_erase_of_mem (mem_erase.mpr ⟨wn a, wH a⟩),
      card_erase_of_mem (zeroH a), hw a 0]
    omega
  have hct : (C false ∩ C true).card = h := hc (fun e => Bool.false_ne_true (vinj e)) 1 1
  obtain ⟨p, hp⟩ := card_pos.mp (show 0 < (C false ∩ C true).card by omega)
  have hpC (j) : p ∈ C j := by
    cases j <;> first | exact (mem_inter.mp hp).1 | exact (mem_inter.mp hp).2
  have room (j) : 2 * h - 2 ≤ ((C j).erase p).card := by
    rw [card_erase_of_mem (hpC j), hw (v j) 1]
    omega
  choose B hBsub hB using fun j => exists_subset_card_eq (room j)
  have hBsub' (j) : B j ⊆ C j := (hBsub j).trans (erase_subset _ _)
  have homogeneous {a b : J} (hab : a ≠ b) : (A a ∩ A b).card ≤ h - 1 := by
    have lt := lost (hAsub a) (hAsub b) (mem_inter.mpr ⟨zeroH a,zeroH b⟩)
      (by simp [A])
    rw [hc hab 0 0] at lt
    omega
  have mixed (a : J) (j : Bool) : (A a ∩ B j).card ≤ h - 1 := by
    by_cases he : a = v j
    · have empty : A a ∩ B j = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨ha',hb'⟩ := mem_inter.mp hx
        have e0 := (level_mem _ _ _).mp (hAsub a ha')
        have e1 := (level_mem _ _ _).mp (hBsub' j hb')
        rw [he] at e0
        exact zero_ne_one (e0.symm.trans e1)
      simp [empty]
    · have lt := lost (hAsub a) (hBsub' j) (mem_inter.mpr ⟨wH a,wC a j he⟩) (by simp [A])
      rw [hc he 0 1] at lt
      omega
  have affine {i j : Bool} (hij : i ≠ j) : (B i ∩ B j).card ≤ h - 1 := by
    have lt := lost (hBsub' i) (hBsub' j) (mem_inter.mpr ⟨hpC i,hpC j⟩) (by
      intro e
      exact (mem_erase.mp (hBsub i (mem_inter.mp e).1)).1 rfl)
    rw [hc (vinj.ne hij) 1 1] at lt
    omega
  have hidx : Fintype.card (J ⊕ Bool) = 4 * h + 1 := by
    rw [Fintype.card_sum, hJ, Fintype.card_bool]
    omega
  have sizes (j : J ⊕ Bool) : (Sum.elim A B j).card = 2 * h - 2 := by
    cases j with
    | inl a => exact hA a
    | inr b => exact hB b
  have pairs : Pairwise fun i j : J ⊕ Bool =>
      (Sum.elim A B i ∩ Sum.elim A B j).card ≤ h - 1 := by
    intro i j hij
    cases i with
    | inl a =>
      cases j with
      | inl b => exact homogeneous (fun e => hij (congrArg Sum.inl e))
      | inr b => exact mixed a b
    | inr a =>
      cases j with
      | inl b =>
        change (B a ∩ A b).card ≤ _
        rw [inter_comm]
        exact mixed b a
      | inr b => exact affine (fun e => hij (congrArg Sum.inr e))
  let e := (Fintype.equivFinOfCardEq hidx).symm
  exact ⟨fun i => Sum.elim A B (e i), fun i => sizes (e i),
    fun _ _ hij => pairs (e.injective.ne hij)⟩

/-- The first unresolved quarter-rate agreement count admits more than one block
length of supports satisfying the pairwise Reed–Solomon intersection bound. -/
theorem production :
    ∃ S : Fin 1073741825 → Finset (Fin 30 → Bit),
      (∀ i, (S i).card = 536870910) ∧ Pairwise fun i j => (S i ∩ S j).card ≤ 268435455 :=
  packing (h := 268435456) (by decide) (by norm_num [Fintype.card_fun, ZMod.card])

/-- The same packing exists on the actual index type of either named evaluation domain. -/
theorem production_on {X : Type} [Fintype X] [DecidableEq X] (hn : Fintype.card X = 2 ^ 30) :
    ∃ S : Fin 1073741825 → Finset X, (∀ i, (S i).card = 536870910) ∧
      Pairwise fun i j => (S i ∩ S j).card ≤ 268435455 := by
  obtain ⟨S, hs, hp⟩ := production
  let e : (Fin 30 → Bit) ≃ X := Fintype.equivOfCardEq (by
    rw [hn]
    norm_num [Fintype.card_fun, ZMod.card])
  refine ⟨fun i => (S i).map e.toEmbedding, fun i => by simpa using hs i, ?_⟩
  intro i j hij
  simpa only [← map_inter, card_map] using hp hij

end ProximityGap.QuarterSupportPackingBarrier
