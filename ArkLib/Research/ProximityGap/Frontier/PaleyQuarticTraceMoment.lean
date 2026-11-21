/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyShiftMultiplicityBudget
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Order.Chebyshev

/-! # The signed fourth moment and distinct quartic branch sets

The elementary symmetric sum on a Paley row counts four distinct sites.
Removing the repeated-site terms and summing over shifts gives an exact
identity with a correction at the shifts where a character entry vanishes.
-/

namespace ProximityGap.PaleyQuarticTraceMoment

open Finset PaleyShiftMultiplicityBudget

private def elementary {α : Type*} (A : Finset α) (f : α → ℤ) (k : ℕ) : ℤ :=
  ∑ I ∈ A.powersetCard k, ∏ x ∈ I, f x

private theorem elementary_insert {α : Type*} [DecidableEq α] {A : Finset α}
    {a : α} (ha : a ∉ A) (f : α → ℤ) (k : ℕ) :
    elementary (insert a A) f (k + 1) = elementary A f (k + 1) + f a * elementary A f k := by
  simp only [elementary, ← esymm_map_val, insert_val_of_notMem ha, Multiset.map_cons,
    Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

/-- Four distinct sites on a row taking values in zero and the two signs. -/
private theorem fourth_elementary {α : Type*} (A : Finset α) (f : α → ℤ)
    (hf : ∀ a, f a = 0 ∨ f a = 1 ∨ f a = -1) :
    let W := ∑ a ∈ A, f a
    let N := ∑ a ∈ A, f a ^ 2
    24 * elementary A f 4 = W ^ 4 - (6 * N - 8) * W ^ 2 + 3 * N ^ 2 - 6 * N := by
  classical
  have one (S : Finset α) : elementary S f 1 = ∑ a ∈ S, f a := by
    simp [elementary, powersetCard_one]
  suffices ∀ S : Finset α,
      let W := ∑ a ∈ S, f a
      let N := ∑ a ∈ S, f a ^ 2
      (2 * elementary S f 2 = W ^ 2 - N) ∧
      (6 * elementary S f 3 = W ^ 3 - (3 * N - 2) * W) ∧
      (24 * elementary S f 4 = W ^ 4 - (6 * N - 8) * W ^ 2 + 3 * N ^ 2 - 6 * N) from
    (this A).2.2
  intro S
  induction S using Finset.induction_on with
  | empty =>
    have empty (n : ℕ) (hn : 0 < n) : (∅ : Finset α).powersetCard n = ∅ :=
      powersetCard_eq_empty.mpr (by simpa using hn)
    simp [elementary, empty]
  | @insert a S ha ih =>
    obtain ⟨h2, h3, h4⟩ := ih
    dsimp only
    simp only [sum_insert ha, elementary_insert ha f 1, elementary_insert ha f 2,
      elementary_insert ha f 3, one]
    rcases hf a with h | h | h <;> rw [h] <;>
      refine ⟨by linear_combination h2, ?_, ?_⟩
    · linear_combination h3
    · linear_combination h4
    · linear_combination h3 + 3 * h2
    · linear_combination h4 + 4 * h3
    · linear_combination h3 - 3 * h2
    · linear_combination h4 - 4 * h3

variable {p : ℕ} [Fact p.Prime]

/-- The quartic character sum with the prescribed branch set. For four distinct
sites its value is minus one minus the smooth projective curve's Frobenius trace. -/
def quarticCharacterSum (I : Finset (ZMod p)) : ℤ :=
  ∑ b : ZMod p, quadraticChar (ZMod p) (∏ a ∈ I, (a + b))

/-- The exact fourth moment at all odd primes, including sets of fewer than four sites. -/
theorem fourth_moment (hp : p ≠ 2) (A : Finset (ZMod p)) :
    ∑ b : ZMod p, shiftSum A b ^ 4 =
      24 * (∑ I ∈ A.powersetCard 4, quarticCharacterSum I) +
        p * (3 * (A.card : ℤ) ^ 2 - 2 * A.card) -
        6 * (A.card : ℤ) ^ 3 + 14 * (A.card : ℤ) ^ 2 - 9 * A.card -
        6 * ∑ a ∈ A, shiftSum A (-a) ^ 2 := by
  classical
  let m : ℤ := A.card
  let W := shiftSum A
  let E (b : ZMod p) := elementary A (fun a => quadraticChar (ZMod p) (a + b)) 4
  have traceSum : ∑ b, E b = ∑ I ∈ A.powersetCard 4, quarticCharacterSum I := by
    simp only [E, elementary, quarticCharacterSum, map_prod]
    rw [sum_comm]
  have poleSum (g : ZMod p → ℤ) :
      (∑ b, if -b ∈ A then g b else 0) = ∑ a ∈ A, g (-a) := by
    have h := (Equiv.neg (ZMod p)).bijective.sum_comp
      (fun a => if a ∈ A then g (-a) else 0)
    simpa only [Equiv.neg_apply, neg_neg, sum_ite_mem, univ_inter] using h
  have row (b : ZMod p) :
      W b ^ 4 = 24 * E b + (6 * m - 8) * W b ^ 2 -
        6 * (if -b ∈ A then W b ^ 2 else 0) +
        (6 * m - 9) * (if -b ∈ A then 1 else 0) + (-3 * m ^ 2 + 6 * m) := by
    let f (a : ZMod p) := quadraticChar (ZMod p) (a + b)
    have signs (a : ZMod p) : f a = 0 ∨ f a = 1 ∨ f a = -1 := by
      by_cases h : a + b = 0
      · exact Or.inl (by simp [f, h])
      · exact Or.inr (quadraticChar_dichotomy h)
    have count : ∑ a ∈ A, f a ^ 2 = m - (if -b ∈ A then 1 else 0) := by
      have sq (a : ZMod p) : f a ^ 2 = 1 - (if a = -b then 1 else 0) := by
        by_cases h : a = -b
        · simp [h, f]
        · have hne : a + b ≠ 0 := fun t => h (eq_neg_of_add_eq_zero_left t)
          rcases quadraticChar_dichotomy hne with hq | hq <;> rw [show f a = _ from hq] <;> simp [h]
      simp_rw [sq]
      simp [sum_sub_distrib, m]
    have h := fourth_elementary A f signs
    change 24 * E b = W b ^ 4 - (6 * (∑ a ∈ A, f a ^ 2) - 8) * W b ^ 2 +
        3 * (∑ a ∈ A, f a ^ 2) ^ 2 - 6 * (∑ a ∈ A, f a ^ 2) at h
    rw [count] at h
    by_cases hzero : -b ∈ A <;> simp only [hzero, ite_true, ite_false] at h ⊢ <;>
      linear_combination -h
  have H := sum_congr (s₁ := (univ : Finset (ZMod p))) rfl (fun b _ => row b)
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, traceSum, poleSum, sum_const,
    nsmul_eq_mul, mul_one, card_univ, ZMod.card] at H
  have second := sum_shift_sq hp A
  change ∑ b, W b ^ 2 = m * p - m ^ 2 at second
  rw [second] at H
  change ∑ b, W b ^ 4 = _
  dsimp only [m, W] at H ⊢
  linear_combination H

/-- A one-sided genus-one bound controls the fourth moment with explicit
diagonal term `3 p |A|²`. -/
theorem fourth_moment_le (hp : p ≠ 2) (A : Finset (ZMod p)) :
    ∑ b : ZMod p, shiftSum A b ^ 4 ≤
      24 * (∑ I ∈ A.powersetCard 4, quarticCharacterSum I) + 3 * p * (A.card : ℤ) ^ 2 := by
  rw [fourth_moment hp A]
  have quad : 0 ≤ 6 * (A.card : ℤ) ^ 2 - 14 * A.card + 9 := by
    nlinarith [sq_nonneg (6 * (A.card : ℤ) - 7)]
  have diag : 0 ≤ ∑ a ∈ A, shiftSum A (-a) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hpm : 0 ≤ (p : ℤ) * A.card := by positivity
  nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℤ) A.card) quad, hpm, diag]

/-- Every partner set obeys the rectangle estimate from the sum of the
distinct quartic branch contributions of the prescribed first set. -/
theorem rectangle_fourth_le (hp : p ≠ 2) (A B : Finset (ZMod p)) :
    |∑ b ∈ B, shiftSum A b| ^ 4 ≤ (B.card : ℤ) ^ 3 *
      (24 * (∑ I ∈ A.powersetCard 4, quarticCharacterSum I) + 3 * p * (A.card : ℤ) ^ 2) := by
  have heven : Even 4 := by decide
  calc
    _ ≤ (∑ b ∈ B, |shiftSum A b|) ^ 4 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_sum_le_sum_abs _ _) 4
    _ ≤ (B.card : ℤ) ^ 3 * ∑ b ∈ B, |shiftSum A b| ^ 4 :=
      pow_sum_le_card_mul_sum_pow (fun _ _ => abs_nonneg _) 3
    _ ≤ (B.card : ℤ) ^ 3 * ∑ b : ZMod p, shiftSum A b ^ 4 := by
      simp_rw [heven.pow_abs]
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (subset_univ B)
        (fun b _ _ => heven.pow_nonneg _)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (fourth_moment_le hp A) (by positivity)

/-- The sum on the full field fixes the normalization of the quartic trace.
For primes at least five, division by the number of four-sets gives
the average character sum `3 / (p - 2)`. -/
theorem complete_quartic_sum (hp : p ≠ 2) :
    8 * (∑ I ∈ (univ : Finset (ZMod p)).powersetCard 4, quarticCharacterSum I) =
      (p : ℤ) * (p - 1) * (p - 3) := by
  have rowZero (b : ZMod p) : shiftSum univ b = 0 := by
    calc
      _ = ∑ x : ZMod p, quadraticChar (ZMod p) x :=
        Fintype.sum_equiv (Equiv.addRight b) _ _ (fun _ => rfl)
      _ = 0 := quadraticChar_sum_zero (by rwa [ZMod.ringChar_zmod_n])
  have h := fourth_moment hp (univ : Finset (ZMod p))
  simp only [rowZero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sum_const_zero, card_univ, ZMod.card, mul_zero, sub_zero] at h
  nlinarith only [h]

/-- The quartic trace sum over all domains of a given size. Every four-set
of branch sites has exactly the same number of containing domains. -/
theorem sum_quartic_over_domains (hp : p ≠ 2) {m : ℕ} (hm : 4 ≤ m) :
    8 * (∑ A ∈ (univ : Finset (ZMod p)).powersetCard m,
      ∑ I ∈ A.powersetCard 4, quarticCharacterSum I) =
      (((p - 4).choose (m - 4) : ℕ) : ℤ) * p * (p - 1) * (p - 3) := by
  classical
  let four := (univ : Finset (ZMod p)).powersetCard 4
  have expand (A : Finset (ZMod p)) :
      ∑ I ∈ A.powersetCard 4, quarticCharacterSum I =
        ∑ I ∈ four, if I ⊆ A then quarticCharacterSum I else 0 := by
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext I
    simp [four, mem_powersetCard, and_comm]
  have count (I : Finset (ZMod p)) (hi : I ∈ four) :
      ∑ A ∈ (univ : Finset (ZMod p)).powersetCard m,
          (if I ⊆ A then quarticCharacterSum I else 0) =
        (((p - 4).choose (m - 4) : ℕ) : ℤ) * quarticCharacterSum I := by
    have h4 := (mem_powersetCard.mp hi).2
    rw [← sum_filter, sum_const, nsmul_eq_mul,
      card_filter_powersetCard_subset I univ m (subset_univ I) (by omega),
      h4, card_univ, ZMod.card]
  simp_rw [expand]
  rw [sum_comm, sum_congr rfl count, ← mul_sum]
  calc
    _ = (((p - 4).choose (m - 4) : ℕ) : ℤ) * (8 * ∑ I ∈ four, quarticCharacterSum I) := by ring
    _ = _ := by
      rw [show 8 * ∑ I ∈ four, quarticCharacterSum I = _ from complete_quartic_sum hp]
      ring

/-- The average character sum per four-set on a uniformly sampled
`m`-domain is exactly `3 / (p - 2)` when `4 ≤ m ≤ p`. The cross-multiplied
identity also covers empty sample spaces. -/
theorem average_quartic (hp : 5 ≤ p) {m : ℕ} (hm : 4 ≤ m) :
    ((p : ℤ) - 2) * (∑ A ∈ (univ : Finset (ZMod p)).powersetCard m,
      ∑ I ∈ A.powersetCard 4, quarticCharacterSum I) =
      3 * ((p.choose m : ℤ) * (m.choose 4 : ℤ)) := by
  have pairs : (p.choose m : ℤ) * (m.choose 4 : ℤ) =
      (p.choose 4 : ℤ) * ((p - 4).choose (m - 4) : ℤ) := by
    exact_mod_cast Nat.choose_mul (n := p) hm
  have descending : (p.descFactorial 4 : ℤ) = 24 * (p.choose 4 : ℤ) := by
    exact_mod_cast (show p.descFactorial 4 = 24 * p.choose 4 by
      rw [Nat.descFactorial_eq_factorial_mul_choose]; rfl)
  norm_num [Nat.descFactorial, Nat.cast_sub (by omega : 3 ≤ p),
    Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_sub (by omega : 1 ≤ p)] at descending
  rw [pairs]
  apply mul_left_cancel₀ (by decide : (8 : ℤ) ≠ 0)
  have total := sum_quartic_over_domains (p := p) (by omega) hm
  linear_combination ((p : ℤ) - 2) * total + ((p - 4).choose (m - 4) : ℤ) * descending

end ProximityGap.PaleyQuarticTraceMoment

#print axioms ProximityGap.PaleyQuarticTraceMoment.fourth_moment

#print axioms ProximityGap.PaleyQuarticTraceMoment.rectangle_fourth_le

#print axioms ProximityGap.PaleyQuarticTraceMoment.sum_quartic_over_domains

#print axioms ProximityGap.PaleyQuarticTraceMoment.average_quartic
