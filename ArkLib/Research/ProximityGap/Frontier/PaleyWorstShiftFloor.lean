/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyShiftMultiplicityBudget

/-!
# A lower bound on the worst prescribed rectangle at sparse sizes

For every coordinate set of size at most half the square root of the prime,
at least as many shifts have a common sign and magnitude above an explicit threshold.
-/

namespace ProximityGap.PaleyWorstShiftFloor

open Finset PaleyShiftMultiplicityBudget
variable {p : ℕ} [Fact p.Prime]

private lemma abs_shift_le (A : Finset (ZMod p)) (b : ZMod p) :
    |shiftSum A b| ≤ (A.card : ℤ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _u ∈ A, (1 : ℤ) := by
      apply sum_le_sum
      intro u _
      by_cases h : u+b=0
      · simp [h]
      · rcases quadraticChar_dichotomy h with he|he <;> simp [he]
    _ = _ := by simp

/-- Every supplied sparse set admits as many same-sign shifts as its cardinality,
each having magnitude strictly above any integer `t` with `2*t² ≤ |A|`. -/
theorem exists_biased_rectangle (hp : p ≠ 2) (A : Finset (ZMod p))
    (hA : A.Nonempty) (hsize : 4*A.card^2 ≤ p) {t : ℕ} (ht : 2*t^2 ≤ A.card) :
    ∃ (σ : ℤ) (B : Finset (ZMod p)), (σ=1 ∨ σ=-1) ∧ B.card=A.card ∧
      (∀ b ∈ B, (t : ℤ) < σ*shiftSum A b) ∧
      (A.card : ℤ)*(t+1) ≤ |∑ b ∈ B, shiftSum A b| := by
  classical
  let a : ℤ := A.card
  let W := shiftSum A
  let P := univ.filter fun b => (t : ℤ) < W b
  let N := univ.filter fun b => W b < -(t : ℤ)
  have hnonneg : 0 ≤ a := by dsimp [a]; positivity
  have hpos : 0 < a := by dsimp [a]; exact_mod_cast hA.card_pos
  have ht' : 2*(t : ℤ)^2 ≤ a := by dsimp [a]; exact_mod_cast ht
  have hsize' : 4*a^2 ≤ (p : ℤ) := by dsimp [a]; exact_mod_cast hsize
  have hlarge : A.card ≤ P.card ∨ A.card ≤ N.card := by
    by_contra! hf
    obtain ⟨h1,h2⟩ := hf
    let E := P ∪ N
    have he : (E.card : ℤ) ≤ 2*a-2 := by
      have hsum := Finset.card_union_le P N
      dsimp [E,a]; omega
    have hrow (b : ZMod p) : 2*(W b)^2 ≤ a+(if b ∈ E then (1:ℤ) else 0)*(2*a^2) := by
      by_cases hb : b ∈ E
      · simp only [hb, ↓reduceIte, one_mul]
        have h := pow_le_pow_left₀ (abs_nonneg (W b)) (abs_shift_le A b) 2
        rw [sq_abs] at h
        change (W b)^2 ≤ a^2 at h
        linarith
      · have hl : -(t : ℤ) ≤ W b ∧ W b ≤ t := by
          simpa [E,P,N,not_or, and_comm] using hb
        have hu := pow_le_pow_left₀ (abs_nonneg (W b)) (abs_le.mpr hl) 2
        rw [sq_abs] at hu
        simp only [hb, ↓reduceIte, zero_mul, add_zero]
        linarith
    have hsum := Finset.sum_le_sum (s := (univ : Finset (ZMod p))) fun b _ => hrow b
    have hc : (∑ b : ZMod p, (if b ∈ E then (1:ℤ) else 0)) = E.card := by simp
    rw [← Finset.mul_sum, sum_add_distrib, ← Finset.sum_mul, hc] at hsum
    simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul] at hsum
    dsimp only [W] at hsum
    rw [sum_shift_sq hp] at hsum
    change 2*(a*p-a^2) ≤ p*a+E.card*(2*a^2) at hsum
    nlinarith only [hsum, mul_nonneg hnonneg (sub_nonneg.mpr hsize'),
      mul_nonneg (sq_nonneg a) (sub_nonneg.mpr he), sq_pos_of_pos hpos]
  obtain ⟨σ,B,hs,hB,hrow⟩ : ∃ (σ : ℤ) (B : Finset (ZMod p)),
      (σ=1 ∨ σ=-1) ∧ B.card=A.card ∧ ∀ b ∈ B, (t : ℤ) < σ*W b := by
    obtain hp'|hn' := hlarge
    · obtain ⟨B,hB,hc⟩ := exists_subset_card_eq hp'
      exact ⟨1,B,Or.inl rfl,hc,fun b hb => by simpa [P] using (hB hb)⟩
    · obtain ⟨B,hB,hc⟩ := exists_subset_card_eq hn'
      refine ⟨-1,B,Or.inr rfl,hc,fun b hb => ?_⟩
      have h : W b < -(t : ℤ) := by simpa [N] using hB hb
      simp; omega
  refine ⟨σ,B,hs,hB,hrow,?_⟩
  have hlow := Finset.sum_le_sum fun b (hb : b ∈ B) => (show (t:ℤ)+1 ≤ σ*W b by
    have := hrow b hb; omega)
  rw [← Finset.mul_sum] at hlow
  simp only [Finset.sum_const,nsmul_eq_mul,hB] at hlow
  change _ ≤ |∑ b ∈ B, W b|
  rcases hs with rfl|rfl
  · simpa using hlow.trans (le_abs_self _)
  · rw [neg_one_mul] at hlow
    exact hlow.trans (neg_le_abs _)

end ProximityGap.PaleyWorstShiftFloor

#print axioms ProximityGap.PaleyWorstShiftFloor.exists_biased_rectangle
