/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pair sums on a fixed cardinality slice

Every ordered pair of distinct elements belongs to the same number of fixed-size subsets.
For symmetric kernels with zero row sums, passing to the complement also counts supersets.
-/

namespace ArkLib.ProximityGap.Frontier.PaleySliceSampling

open Finset

variable {α : Type*} [DecidableEq α]

/-- Sum of a kernel over the ordered pairs of a finite set. -/
def pairSum (K : α → α → ℝ) (S : Finset α) : ℝ := ∑ x ∈ S, ∑ y ∈ S, K x y

private theorem pairSum_eq_sum_over (K : α → α → ℝ) {S T : Finset α} (hST : S ⊆ T) :
    pairSum K S = ∑ e ∈ T ×ˢ T, if {e.1, e.2} ⊆ S then K e.1 e.2 else 0 := by
  have hf : (T ×ˢ T).filter (fun e => {e.1, e.2} ⊆ S) = S ×ˢ S := by
    ext e
    simp only [mem_filter, mem_product, insert_subset_iff, singleton_subset_iff]
    exact ⟨And.right, fun h => ⟨⟨hST h.1, hST h.2⟩, h⟩⟩
  rw [← sum_filter, hf, sum_product, pairSum]

/-- Exact sum over the `m`-element subsets of a prescribed set, for every zero-diagonal kernel. -/
theorem sum_pairSum_subsets (K : α → α → ℝ) (hdiag : ∀ x, K x x = 0)
    (T : Finset α) {m : ℕ} (hm : 2 ≤ m) :
    ∑ S ∈ T.powersetCard m, pairSum K S =
      ((T.card - 2).choose (m - 2) : ℝ) * pairSum K T := by
  classical
  have hrow (e : α × α) (he : e ∈ T ×ˢ T) :
      (∑ S ∈ T.powersetCard m, if {e.1, e.2} ⊆ S then K e.1 e.2 else 0) =
        ((T.card - 2).choose (m - 2) : ℝ) * K e.1 e.2 := by
    by_cases h : e.1 = e.2
    · simp [h, hdiag]
    have hpair : ({e.1, e.2} : Finset α).card = 2 := by simp [h]
    have hsub : ({e.1, e.2} : Finset α) ⊆ T := by
      simpa only [insert_subset_iff, singleton_subset_iff] using mem_product.mp he
    rw [← sum_filter, sum_const, nsmul_eq_mul,
      card_filter_powersetCard_subset _ _ _ hsub (hpair ▸ hm), hpair]
  calc
    _ = ∑ S ∈ T.powersetCard m,
        ∑ e ∈ T ×ˢ T, if {e.1, e.2} ⊆ S then K e.1 e.2 else 0 :=
      sum_congr rfl fun S hS => pairSum_eq_sum_over K (mem_powersetCard.mp hS).1
    _ = _ := by rw [sum_comm, sum_congr rfl hrow, ← mul_sum, sum_product, pairSum]

/-- Complementing preserves the pair sum of a symmetric kernel whose row sums vanish. -/
theorem pairSum_compl [Fintype α] (K : α → α → ℝ) (hsymm : ∀ x y, K x y = K y x)
    (hzero : ∀ x, ∑ y, K x y = 0) (T : Finset α) : pairSum K Tᶜ = pairSum K T := by
  have hsplit (S : Finset α) : (∑ x ∈ S, ∑ y ∈ Sᶜ, K x y) + pairSum K S = 0 := by
    rw [pairSum, ← sum_add_distrib]
    simp only [sum_compl_add_sum, hzero, sum_const_zero]
  have hcross : (∑ x ∈ Tᶜ, ∑ y ∈ T, K x y) = ∑ y ∈ T, ∑ x ∈ Tᶜ, K y x := by
    rw [sum_comm]
    exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => hsymm x y
  have h := hsplit Tᶜ
  rw [compl_compl, hcross] at h
  linarith [hsplit T]

/-- Exact sum over the `m`-element supersets of a marked set, obtained by sampling complements. -/
theorem sum_pairSum_supersets [Fintype α] (K : α → α → ℝ) (hdiag : ∀ x, K x x = 0)
    (hsymm : ∀ x y, K x y = K y x) (hzero : ∀ x, ∑ y, K x y = 0)
    (T : Finset α) {m : ℕ} (hm : 2 ≤ Fintype.card α - m) :
    ∑ S ∈ ((univ : Finset α).powersetCard m).filter (T ⊆ ·), pairSum K S =
      ((Fintype.card α - T.card - 2).choose (Fintype.card α - m - 2) : ℝ) *
        pairSum K T := by
  classical
  have hle : m ≤ Fintype.card α := by omega
  calc
    _ = ∑ U ∈ Tᶜ.powersetCard (Fintype.card α - m), pairSum K U := by
      apply sum_bij' (fun S _ => Sᶜ) (fun U _ => Uᶜ)
      · exact fun S _ => compl_compl S
      · exact fun U _ => compl_compl U
      · exact fun S _ => (pairSum_compl K hsymm hzero S).symm
      · intro S hS
        obtain ⟨hSm, hTS⟩ := mem_filter.mp hS
        exact mem_powersetCard.mpr ⟨compl_subset_compl.mpr hTS,
          by rw [card_compl, (mem_powersetCard.mp hSm).2]⟩
      · intro U hU
        obtain ⟨hUT, hUm⟩ := mem_powersetCard.mp hU
        refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, ?_⟩, ?_⟩
        · rw [card_compl, hUm]
          omega
        · simpa using compl_subset_compl.mpr hUT
    _ = _ := by rw [sum_pairSum_subsets K hdiag _ hm, card_compl, pairSum_compl K hsymm hzero]

/-- A uniform bound `b` on the sampled subsets bounds the marked set after scaling by
the ratio of its pair count to the sample pair count. -/
theorem abs_pairSum_mul_choose_le_of_subsets (K : α → α → ℝ) (hdiag : ∀ x, K x x = 0)
    (T : Finset α) {m : ℕ} (hm : 2 ≤ m) (hmT : m ≤ T.card) {b : ℝ}
    (hbound : ∀ S ∈ T.powersetCard m, |pairSum K S| ≤ b) :
    |pairSum K T| * (m.choose 2 : ℝ) ≤ (T.card.choose 2 : ℝ) * b := by
  let c : ℝ := (T.card - 2).choose (m - 2)
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast Nat.choose_pos (Nat.sub_le_sub_right hmT 2)
  have hb : c * |pairSum K T| ≤ (T.card.choose m : ℝ) * b := calc
    _ = |∑ S ∈ T.powersetCard m, pairSum K S| := by
      rw [sum_pairSum_subsets K hdiag _ hm, abs_mul, abs_of_pos hc]
    _ ≤ ∑ S ∈ T.powersetCard m, |pairSum K S| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ T.powersetCard m, b := sum_le_sum hbound
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_powersetCard]
  have hchoose : (T.card.choose m : ℝ) * (m.choose 2 : ℝ) = (T.card.choose 2 : ℝ) * c := by
    dsimp [c]
    exact_mod_cast Nat.choose_mul (n := T.card) hm
  apply le_of_mul_le_mul_left (a := c) _ hc
  calc
    _ = (c * |pairSum K T|) * (m.choose 2 : ℝ) := by ac_rfl
    _ ≤ ((T.card.choose m : ℝ) * b) * (m.choose 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _)
    _ = ((T.card.choose m : ℝ) * (m.choose 2 : ℝ)) * b := by ac_rfl
    _ = _ := by rw [hchoose]; ac_rfl

/-- A uniform bound on fixed-size supersets transfers with the ratio of their complement
pair counts. This also covers marked sets of size zero or one. -/
theorem abs_pairSum_mul_choose_le_of_supersets [Fintype α] (K : α → α → ℝ)
    (hdiag : ∀ x, K x x = 0) (hsymm : ∀ x y, K x y = K y x)
    (hzero : ∀ x, ∑ y, K x y = 0) (T : Finset α) {m : ℕ}
    (hm : 2 ≤ Fintype.card α - m) (hTm : T.card ≤ m) {b : ℝ}
    (hbound : ∀ S : Finset α, T ⊆ S → S.card = m → |pairSum K S| ≤ b) :
    |pairSum K T| * ((Fintype.card α - m).choose 2 : ℝ) ≤
      ((Fintype.card α - T.card).choose 2 : ℝ) * b := by
  have hle : Fintype.card α - m ≤ Tᶜ.card := by rw [card_compl]; omega
  have h := abs_pairSum_mul_choose_le_of_subsets K hdiag Tᶜ hm hle (b := b) (by
    intro U hU
    obtain ⟨hUT, hUm⟩ := mem_powersetCard.mp hU
    rw [← pairSum_compl K hsymm hzero U]
    apply hbound Uᶜ (by simpa using compl_subset_compl.mpr hUT)
    rw [card_compl, hUm]
    omega)
  simpa only [card_compl, pairSum_compl K hsymm hzero] using h

/-- The sum on a prescribed rectangle. -/
def cutSum (K : α → α → ℝ) (A B : Finset α) : ℝ := ∑ x ∈ A, ∑ y ∈ B, K x y

private theorem cut_indicator [Fintype α] (K : α → α → ℝ) (A B : Finset α) :
    cutSum K A B =
      ∑ x : α, ∑ y : α, if x ∈ A then (if y ∈ B then K x y else 0) else 0 := by
  have h (x : α) : (∑ y : α, if x ∈ A then (if y ∈ B then K x y else 0) else 0) =
      if x ∈ A then ∑ y ∈ B, K x y else 0 := by
    by_cases hx : x ∈ A <;> simp [hx, sum_ite_mem]
  simp_rw [h]
  rw [sum_ite_mem, univ_inter, cutSum]

/-- Polarization of an arbitrary rectangle keeps the intersection term when the sets overlap. -/
theorem cut_polarization [Fintype α] (K : α → α → ℝ) (hsymm : ∀ x y, K x y = K y x)
    (A B : Finset α) :
    2 * cutSum K A B = pairSum K (A ∪ B) - pairSum K (A \ B) -
      pairSum K (B \ A) + pairSum K (A ∩ B) := by
  have hswap : cutSum K A B = cutSum K B A := by
    unfold cutSum
    rw [sum_comm]
    exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => hsymm x y
  change 2 * cutSum K A B = cutSum K _ _ - cutSum K _ _ - cutSum K _ _ + cutSum K _ _
  rw [two_mul]
  conv_lhs => rhs; rw [hswap]
  simp only [cut_indicator, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
    by_cases hyA : y ∈ A <;> by_cases hyB : y ∈ B <;> simp [hxA, hxB, hyA, hyB]

private theorem sum_sample (f : α → ℝ) (T : Finset α) {m : ℕ} (hm : 1 ≤ m) :
    ∑ S ∈ T.powersetCard m, ∑ x ∈ S, f x =
      ((T.card - 1).choose (m - 1) : ℝ) * ∑ x ∈ T, f x := by
  classical
  have hpart (S : Finset α) (hS : S ∈ T.powersetCard m) :
      (∑ x ∈ S, f x) = ∑ x ∈ T, if x ∈ S then f x else 0 := by
    rw [sum_ite_mem, inter_eq_right.mpr (mem_powersetCard.mp hS).1]
  have hrow (x : α) (hx : x ∈ T) :
      (∑ S ∈ T.powersetCard m, if x ∈ S then f x else 0) =
        ((T.card - 1).choose (m - 1) : ℝ) * f x := by
    simp_rw [← singleton_subset_iff (a := x)]
    rw [← sum_filter, sum_const, nsmul_eq_mul,
      card_filter_powersetCard_subset _ _ _ (singleton_subset_iff.mpr hx) (by simpa using hm)]
    simp
  rw [sum_congr rfl hpart, sum_comm, sum_congr rfl hrow, mul_sum]

private theorem abs_sum_mul_card_sample (f : α → ℝ) (T : Finset α) {m : ℕ} (hm : 1 ≤ m)
    (hmT : m ≤ T.card) {b : ℝ} (hbound : ∀ S ∈ T.powersetCard m, |∑ x ∈ S, f x| ≤ b) :
    |∑ x ∈ T, f x| * m ≤ T.card * b := by
  let c : ℝ := (T.card - 1).choose (m - 1)
  have hc : 0 < c := by dsimp [c]; exact_mod_cast Nat.choose_pos (Nat.sub_le_sub_right hmT 1)
  have h : c * |∑ x ∈ T, f x| ≤ (T.card.choose m : ℝ) * b := calc
    _ = |∑ S ∈ T.powersetCard m, ∑ x ∈ S, f x| := by
      rw [sum_sample f T hm, abs_mul, abs_of_pos hc]
    _ ≤ _ := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ T.powersetCard m, b := sum_le_sum hbound
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_powersetCard]
  have hchoose : (T.card.choose m : ℝ) * m = T.card * c := by
    dsimp [c]
    exact_mod_cast (by simpa using (Nat.choose_mul (n := T.card) hm))
  apply le_of_mul_le_mul_left (a := c) _ hc
  calc
    _ = (c * |∑ x ∈ T, f x|) * m := by ac_rfl
    _ ≤ ((T.card.choose m : ℝ) * b) * m := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)
    _ = ((T.card.choose m : ℝ) * m) * b := by ac_rfl
    _ = _ := by rw [hchoose]; ac_rfl

private theorem choose_twice_le {m : ℕ} (hm : 2 ≤ m) :
    (((2*m).choose 2 : ℕ) : ℝ) ≤ 6 * (m.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (sub_nonneg.mpr hm')]

private theorem choose_compl_le {N m : ℕ} (hm : 2 ≤ m) (hN : 4*m ≤ N) :
    (N.choose 2 : ℝ) ≤ 2 * ((N-m).choose 2 : ℝ) := by
  have hmn : m ≤ N := by omega
  have ha : (3:ℝ)*N ≤ 4*(N - (m:ℝ)) := by exact_mod_cast (show 3*N ≤ 4*(N-m) by omega)
  have hb : (2:ℝ)*(N-1) ≤ 3*(N - (m:ℝ)-1) := by
    have hNr : (4:ℝ)*m ≤ N := by exact_mod_cast hN
    have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hn : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hc := mul_le_mul ha hb (by linarith : (0:ℝ) ≤ 2*(N-1))
    (by linarith : (0:ℝ) ≤ 4*(N-(m:ℝ)))
  rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_sub hmn]
  nlinarith only [hc]

private theorem bounds_near_slice [Fintype α] (K : α → α → ℝ) (hd : ∀ x, K x x = 0)
    (hs : ∀ x y, K x y = K y x) (hz : ∀ x, ∑ y, K x y = 0)
    {m : ℕ} (hm : 2 ≤ m) (hN : 4*m ≤ Fintype.card α) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ S : Finset α, S.card = m → |pairSum K S| ≤ b) :
    (∀ S : Finset α, S.card ≤ m → |pairSum K S| ≤ 2*b) ∧
      (∀ S : Finset α, S.card ≤ 2*m → |pairSum K S| ≤ 6*b) := by
  have hsmall (S : Finset α) (hSm : S.card ≤ m) : |pairSum K S| ≤ 2*b := by
    have hq : 2 ≤ Fintype.card α - m := by omega
    have h := abs_pairSum_mul_choose_le_of_supersets K hd hs hz S hq hSm
      (fun U _ hU => hbound U hU)
    have hc : 0 < (((Fintype.card α-m).choose 2 : ℕ) : ℝ) := by exact_mod_cast Nat.choose_pos hq
    have hmono : (((Fintype.card α-S.card).choose 2 : ℕ) : ℝ) ≤ (Fintype.card α).choose 2 := by
      exact_mod_cast Nat.choose_le_choose 2 (Nat.sub_le _ _)
    apply le_of_mul_le_mul_right (a := (((Fintype.card α-m).choose 2 : ℕ) : ℝ)) _ hc
    calc
      _ ≤ _ := h
      _ ≤ _ := mul_le_mul_of_nonneg_right (hmono.trans (choose_compl_le hm hN)) hb
      _ = _ := by ac_rfl
  refine ⟨hsmall, fun S hSm => ?_⟩
  rcases le_total S.card m with h | h
  · linarith [hsmall S h]
  · have H := abs_pairSum_mul_choose_le_of_subsets K hd S hm h
      (fun U hU => hbound U (mem_powersetCard.mp hU).2)
    have hmono : (S.card.choose 2 : ℝ) ≤ ((2*m).choose 2 : ℝ) := by
      exact_mod_cast Nat.choose_le_choose 2 hSm
    have hc : 0 < (m.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos hm
    apply le_of_mul_le_mul_right (a := (m.choose 2 : ℝ)) _ hc
    calc
      _ ≤ _ := H
      _ ≤ _ := mul_le_mul_of_nonneg_right (hmono.trans (choose_twice_le hm)) hb
      _ = _ := by ac_rfl

/-- A single-cardinality test for all sufficiently large rectangles. The kernel is symmetric,
has zero diagonal and row sums, and the ambient set has at least `4*m` elements.
The hypothesis only tests squares `S × S` with exactly `m` vertices. -/
theorem cut_bound_of_one_size [Fintype α] (K : α → α → ℝ) (hd : ∀ x, K x x = 0)
    (hs : ∀ x y, K x y = K y x) (hz : ∀ x, ∑ y, K x y = 0)
    {m : ℕ} (hm : 2 ≤ m) (hN : 4*m ≤ Fintype.card α) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ S : Finset α, S.card = m → |pairSum K S| ≤ b)
    (A B : Finset α) (hA : m ≤ A.card) (hB : m ≤ B.card) :
    |cutSum K A B| * (m : ℝ)^2 ≤ 6*b*A.card*B.card := by
  have hm1 : 1 ≤ m := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨hsmall, hlarge⟩ := bounds_near_slice K hd hs hz hm hN hb hbound
  have hfixed (X Y : Finset α) (hX : X.card = m) (hY : Y.card = m) :
      |cutSum K X Y| ≤ 6*b := by
    have hU := abs_le.mp (hlarge (X ∪ Y) (by
      have := card_union_le X Y; omega))
    have hD := abs_le.mp (hsmall (X \ Y) ((card_le_card sdiff_subset).trans hX.le))
    have hE := abs_le.mp (hsmall (Y \ X) ((card_le_card sdiff_subset).trans hY.le))
    have hI := abs_le.mp (hsmall (X ∩ Y) ((card_le_card inter_subset_left).trans hX.le))
    have hpol := cut_polarization K hs X Y
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hpart (X : Finset α) (hX : X ∈ A.powersetCard m) :
      |∑ x ∈ X, ∑ y ∈ B, K x y| ≤ B.card*(6*b)/m := by
    apply (le_div_iff₀ hmr).mpr
    rw [sum_comm]
    refine abs_sum_mul_card_sample (fun y => ∑ x ∈ X, K x y) B hm1 hB fun Y hY => ?_
    rw [sum_comm]
    exact hfixed X Y (mem_powersetCard.mp hX).2 (mem_powersetCard.mp hY).2
  have h := abs_sum_mul_card_sample (fun x => ∑ y ∈ B, K x y) A hm1 hA hpart
  calc
    _ = (|∑ x ∈ A, ∑ y ∈ B, K x y| * m) * m := by rw [cutSum, pow_two]; ac_rfl
    _ ≤ (A.card * (B.card*(6*b)/m)) * m := mul_le_mul_of_nonneg_right h hmr.le
    _ = _ := by rw [mul_assoc, div_mul_cancel₀ _ hmr.ne']; ac_rfl

end ArkLib.ProximityGap.Frontier.PaleySliceSampling

#print axioms ArkLib.ProximityGap.Frontier.PaleySliceSampling.sum_pairSum_subsets
#print axioms ArkLib.ProximityGap.Frontier.PaleySliceSampling.sum_pairSum_supersets

#print axioms ArkLib.ProximityGap.Frontier.PaleySliceSampling.abs_pairSum_mul_choose_le_of_supersets

#print axioms ArkLib.ProximityGap.Frontier.PaleySliceSampling.cut_bound_of_one_size
