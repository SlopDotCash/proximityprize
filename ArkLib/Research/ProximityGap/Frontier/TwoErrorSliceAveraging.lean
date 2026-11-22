/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic

/-! # Averaging weighted samples and removing antipodal error pairs -/

namespace ProximityGap.TwoErrorSliceAveraging
open Finset

/-- Each weighted sample occurs once for each of its members when extended
from a predecessor sample. -/
theorem extension_sum {I : Type*} [DecidableEq I] (G : Finset I) (r : ℕ)
    (w : Finset I → ℕ) :
    ∑ Q ∈ G.powersetCard r, ∑ x ∈ G \ Q, w (insert x Q) =
      (r+1) * ∑ S ∈ G.powersetCard (r+1), w S := by
  classical
  calc
    _ = ∑ z ∈ (G.powersetCard r).sigma (fun Q => G \ Q), w (insert z.2 z.1) :=
      sum_sigma' _ _ _
    _ = ∑ z ∈ (G.powersetCard (r+1)).sigma id, w z.1 := by
      refine sum_bij' (fun z _ => ⟨insert z.2 z.1,z.2⟩) (fun z _ => ⟨z.1.erase z.2,z.2⟩) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨Q,x⟩ hz
        obtain ⟨hQ,hx⟩ := mem_sigma.mp hz
        obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hQ
        obtain ⟨hxG,hxQ⟩ := mem_sdiff.mp hx
        change (Sigma.mk (β:=fun _ : Finset I => I) (insert x Q) x) ∈ (G.powersetCard (r+1)).sigma id
        exact mem_sigma.mpr ⟨mem_powersetCard.mpr
          ⟨insert_subset hxG hsub,by simp [hxQ,hcard]⟩,mem_insert_self ..⟩
      · rintro ⟨S,x⟩ hz
        obtain ⟨hS,hx⟩ := mem_sigma.mp hz
        obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hS
        change x∈S at hx
        change S.card=r+1 at hcard
        change (Sigma.mk (β:=fun _ : Finset I => I) (S.erase x) x) ∈ (G.powersetCard r).sigma (fun Q => G \ Q)
        exact mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨(erase_subset ..).trans hsub,by
          rw [card_erase_of_mem hx,hcard]; omega⟩,mem_sdiff.mpr ⟨hsub hx,notMem_erase x S⟩⟩
      · rintro ⟨Q,x⟩ hz
        have hn := (mem_sdiff.mp (mem_sigma.mp hz).2).2
        simp [erase_insert hn]
      · rintro ⟨S,x⟩ hz
        exact congrArg (fun T => Sigma.mk T x) (insert_erase (mem_sigma.mp hz).2)
      · intros; rfl
    _ = _ := by
      rw [sum_sigma, mul_sum]
      exact sum_congr rfl fun S hS => by simp [(mem_powersetCard.mp hS).2]

/-- Average a bound on all one-site extensions of each predecessor sample. -/
theorem sample_average_general {I : Type*} [DecidableEq I] (G : Finset I) (l b N : ℕ)
    (w : Finset I → ℕ) (hl : 0<l)
    (h : ∀ Q ∈ G.powersetCard (l-1), b ≤ ∑ x ∈ G \ Q, w (insert x Q))
    (hN : G.card-l+1=N) (hroom : l≤G.card) :
    G.card.choose l * b ≤ N * ∑ S ∈ G.powersetCard l, w S := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  simp only [Nat.succ_sub_one] at h
  have bound := sum_le_sum h
  rw [extension_sum] at bound
  simp only [sum_const,card_powersetCard,smul_eq_mul] at bound
  have steps := Nat.choose_succ_right_eq G.card r
  rw [show G.card-r=N by omega] at steps
  apply Nat.le_of_mul_le_mul_right (c:=r+1)
  · calc
      G.card.choose (r+1)*b*(r+1) = G.card.choose r*b*N := by
        calc
          _ = (G.card.choose (r+1)*(r+1))*b := by ring
          _ = _ := by rw [steps]; ring
      _ ≤ ((r+1) * ∑ S ∈ G.powersetCard (r+1), w S) * N := Nat.mul_le_mul_right _ bound
      _ = (N * ∑ S ∈ G.powersetCard (r+1), w S) * (r+1) := by ring
  · omega

/-- On 66 possible extensions, a sample has mean weight at least 186/66
whenever every predecessor admits total extension weight at least 186. -/
theorem sample_average {I : Type*} [DecidableEq I] (G : Finset I) (l : ℕ)
    (w : Finset I → ℕ) (hl : 0<l)
    (h : ∀ Q ∈ G.powersetCard (l-1), 186 ≤ ∑ x ∈ G \ Q, w (insert x Q))
    (h66 : G.card-l+1=66) (hroom : l≤G.card) :
    G.card.choose l * 186 ≤ 66 * ∑ S ∈ G.powersetCard l, w S :=
  sample_average_general G l 186 66 w hl h h66 hroom

/-- Antipodal pairs form a matching in every injective field domain. -/
theorem clean_pairs_lower {I F : Type*} [DecidableEq I] [Field F] [DecidableEq F]
    (D : I ↪ F) (E : Finset I) :
    E.card.choose 2 - E.card/2 ≤
      ((E.powersetCard 2).filter fun A => ∀ u∈A, ∀ v∈A, u≠v → D u ≠ -D v).card := by
  classical
  let clean (A : Finset I) := ∀ u∈A, ∀ v∈A, u≠v → D u≠ -D v
  let P := E.powersetCard 2
  let B := P.filter (fun A => ¬clean A)
  have repr (A : Finset I) (hA : A∈B) (x : I) (hx : x∈A) :
      ∃ y : I, D x = -D y ∧ A={x,y} := by
    obtain ⟨hP,hn⟩ := mem_filter.mp hA
    have count := (mem_powersetCard.mp hP).2
    change ¬(∀ u∈A, ∀ v∈A, u≠v → D u≠ -D v) at hn
    push Not at hn
    obtain ⟨u,hu,v,hv,hne,heq⟩ := hn
    have eq : {u,v}=A := eq_of_subset_of_card_le (insert_subset hu (singleton_subset_iff.mpr hv)) (by simp [hne,count])
    rw [← eq] at hx ⊢
    rcases mem_insert.mp hx with rfl|hvx
    · exact ⟨v,heq,rfl⟩
    · rcases mem_singleton.mp hvx with rfl
      exact ⟨u,neg_eq_iff_eq_neg.mp heq.symm,pair_comm ..⟩
  have dis : (B : Set (Finset I)).PairwiseDisjoint id := by
    intro A hA C hC hne
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨v,hv,rfl⟩ := repr A hA x hx
    obtain ⟨v',hv',rfl⟩ := repr C hC x hy
    exact hne (by rw [D.injective (neg_injective (hv.symm.trans hv'))])
  have cover : B.biUnion id ⊆ E := biUnion_subset.mpr fun _ hA =>
    (mem_powersetCard.mp (mem_filter.mp hA).1).1
  have matchSize := card_le_card cover
  rw [card_biUnion dis] at matchSize
  have sumSize : ∑ A ∈ B, (id A).card = B.card*2 := by
    calc
      _ = ∑ _A ∈ B, 2 := sum_congr rfl fun A hA =>
        (mem_powersetCard.mp (mem_filter.mp hA).1).2
      _ = _ := by simp
  rw [sumSize] at matchSize
  have count := card_filter_add_card_filter_not (s:=P) clean
  change (P.filter clean).card+B.card=P.card at count
  have total : P.card=E.card.choose 2 := card_powersetCard ..
  change _ ≤ (P.filter clean).card
  omega

end ProximityGap.TwoErrorSliceAveraging
#print axioms ProximityGap.TwoErrorSliceAveraging.sample_average
#print axioms ProximityGap.TwoErrorSliceAveraging.clean_pairs_lower
