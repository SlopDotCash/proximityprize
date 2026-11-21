/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! # Disjoint short relations inside every projection onto subgroup block representatives -/

namespace ArkLib.ProximityGap.Frontier.ProjectedShortRelations
open Finset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The support of a nonzero balanced relation with coefficients in {-1,0,1}. -/
def BalancedSupport (t : ℕ) (U : Finset G) : Prop :=
  ∃ A B : Finset G, A.Nonempty ∧ Disjoint A B ∧ A.card = B.card ∧ A.card ≤ t ∧
    U = A ∪ B ∧ ∑ x ∈ A, x = ∑ x ∈ B, x

theorem balancedSupport_size {t : ℕ} {U : Finset G} (h : BalancedSupport t U) :
    U.Nonempty ∧ U.card ≤ 2*t := by
  obtain ⟨A,B,hA,hAB,hEq,ht,rfl,_⟩ := h
  exact ⟨hA.mono subset_union_left, by rw [card_union_of_disjoint hAB]; omega⟩

theorem balancedSupport_of_threshold [Fintype G] {t : ℕ} (W : Finset G)
    (hbig : Fintype.card G < W.card.choose t) :
    ∃ U ⊆ W, BalancedSupport t U := by
  classical
  have hcard : (univ : Finset G).card < (W.powersetCard t).card := by simpa using hbig
  obtain ⟨S,hS,T,hT,hne,he⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (f := fun A : Finset G ↦ ∑ x ∈ A, x) hcard (fun _ _ ↦ mem_univ _)
  obtain ⟨hSW,hSc⟩ := mem_powersetCard.mp hS
  obtain ⟨hTW,hTc⟩ := mem_powersetCard.mp hT
  have hAc : (S \ T).card = (T \ S).card := by
    rw [card_sdiff, card_sdiff, inter_comm]
    omega
  have hn : (S \ T).Nonempty := by
    by_contra! hh
    have hsub := sdiff_eq_empty_iff_subset.mp hh
    exact hne (eq_of_subset_of_card_le hsub (by omega))
  refine ⟨(S \ T) ∪ (T \ S), union_subset (sdiff_subset.trans hSW) (sdiff_subset.trans hTW),
    S \ T, T \ S, hn, ?_, hAc, (card_le_card sdiff_subset).trans hSc.le, rfl,
    sum_sdiff_eq_sum_sdiff_iff.mpr he⟩
  exact disjoint_left.mpr (fun x hx hy ↦ (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1)

/-- Greedy deletion yields disjoint supports, hence independent signed vectors in the congruence
lattice. The loss per extraction is at most twice the subset size. -/
theorem disjoint_balanced_supports [Fintype G] {b t : ℕ} (hb : Fintype.card G < b.choose t)
    (J : ℕ) (W : Finset G) (hsize : b + 2*t*J ≤ W.card + 2*t) :
    ∃ C : Finset (Finset G), C.card = J ∧
      (∀ U ∈ C, U ⊆ W ∧ BalancedSupport t U) ∧ (C : Set (Finset G)).PairwiseDisjoint id := by
  classical
  induction J generalizing W with
  | zero => exact ⟨∅,rfl,by simp,by simp⟩
  | succ J ih =>
    rw [Nat.mul_succ] at hsize
    have hBW : b ≤ W.card := by omega
    obtain ⟨U,hUW,hU⟩ := balancedSupport_of_threshold W (hb.trans_le (Nat.choose_le_choose t hBW))
    obtain ⟨hUn,hUc⟩ := balancedSupport_size hU
    have hsmall : b + 2*t*J ≤ (W \ U).card + 2*t := by
      rw [card_sdiff_of_subset hUW]
      have := card_le_card hUW
      omega
    obtain ⟨C,hC,hsub,hdisj⟩ := ih (W \ U) hsmall
    have hn : U ∉ C := by
      intro hc
      obtain ⟨x,hx⟩ := hUn
      exact (mem_sdiff.mp ((hsub U hc).1 hx)).2 hx
    refine ⟨insert U C,by simp [hn,hC], ?_, ?_⟩
    · intro V hV
      rcases mem_insert.mp hV with rfl | hV
      · exact ⟨hUW,hU⟩
      · exact ⟨(hsub V hV).1.trans sdiff_subset,(hsub V hV).2⟩
    · rw [coe_insert, Set.pairwiseDisjoint_insert_of_notMem hn]
      refine ⟨hdisj, ?_⟩
      intro V hV
      exact disjoint_left.mpr (fun x hx hy ↦ (mem_sdiff.mp ((hsub V hV).1 hy)).2 hx)

/-- The larger named production prime is already smaller than this seven-subset collision
threshold. The conclusion applies to an arbitrary extraction of one point from each of the
2^26 cosets of an order-sixteen subgroup. -/
theorem at_production_threshold [Fintype G]
    (hp : Fintype.card G ≤ 730750818665451459101842416358141509841924915201)
    (W : Finset G) (hcard : W.card = 2^26) :
    ∃ C : Finset (Finset G), C.card = 3132099 ∧
      (∀ U ∈ C, U ⊆ W ∧ BalancedSupport 7 U) ∧ (C : Set (Finset G)).PairwiseDisjoint id := by
  apply disjoint_balanced_supports (b := 23259482)
  · apply hp.trans_lt
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
  · rw [hcard]
    decide +kernel

#print axioms disjoint_balanced_supports
#print axioms at_production_threshold
end ArkLib.ProximityGap.Frontier.ProjectedShortRelations
