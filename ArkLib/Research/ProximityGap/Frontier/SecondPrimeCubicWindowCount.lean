/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticInterpolation

/-! # Exact cardinal bounds for the unrestricted cubic auxiliary window -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeCubicWindowCount
open Finset SecondPrimeQuarticInterpolation

abbrev Vars (t : ℕ) := Monomials 400000000 170 67108863 t

set_option maxRecDepth 4096 in
/-- Exact number of coefficients in the full auxiliary. -/
theorem source_card : Fintype.card (Vars 11453246176) = 393231054340117065366 := by
  simp only [Vars, Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  decide

set_option maxRecDepth 4096 in
/-- Uniform linear upper bound on the smaller multiplier window. The first 167 value
degrees have full coordinate rows throughout the weight interval; the remaining four are
bounded at the smallest admissible weight. -/
theorem multiplier_card (w : ℕ) (h₀ : 201326589 ≤ w) (h₁ : w ≤ 290805098) :
    Fintype.card (Vars (11453246176 - w)) + 167 * (400000001*w) ≤
      400000001*982540900815 := by
  let a (j : Fin 171) := if j.val < 167 then 11453246176-j.val*67108863 else
    (11453246176-201326589)-j.val*67108863
  let b (j : Fin 171) : ℕ := if j.val < 167 then 1 else 0
  have hi (j : Fin 171) :
      (400000001-j.val)*((11453246176-w)-j.val*67108863) + 400000001*w*b j ≤
        400000001*a j := by
    have hle := Nat.mul_le_mul_right ((11453246176-w)-j.val*67108863)
      (Nat.sub_le 400000001 j.val)
    by_cases hj : j.val < 167
    · simp only [a, b, hj, ite_true, mul_one]
      omega
    · simp only [a, b, hj, ite_false, mul_zero, add_zero]
      omega
  have aa : ∑ j, a j = 982540900815 := by decide
  have bb : ∑ j, b j = 167 := by decide
  have hsum := sum_le_sum (s := (univ : Finset (Fin 171))) (fun j _ => hi j)
  simp only [sum_add_distrib, ← mul_sum, aa, bb] at hsum
  simp only [Vars, Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  change (∑ j : Fin 171, (400000001-j.val)*((11453246176-w)-j.val*67108863)) + _ ≤ _
  omega

/-- Either the ordinary-polar charge or the direct Hessian charge at large weight
pays the cost of the unrestricted cubic auxiliary. -/
def SufficientCharge (r w : ℕ) : Prop :=
  3 * r + 35 * 67108863 ≤ 2 * 1073741824 + 16 * w + 532 ∨
    220000000 ≤ w ∧ 7 * r + 27 * 67108863 ≤ 6 * 1073741824 + 16 * w

/-- The actual independent polynomial jet columns leave enough room outside all multiples
at every possible weight, subject to the ordinary-polar received-order inequality. -/
theorem dimension_surplus {I : Type} [Fintype I] (r : I → ℕ) (w : ℕ)
    (h₀ : 201326589 ≤ w) (h₁ : w ≤ 290805098) (hn : Fintype.card I = 1073741824)
    (hr : ∀ x, r x ≤ 3)
    (hcharge : SufficientCharge (∑ x, r x) w) :
    Fintype.card I * (528*400000001) + Fintype.card (Vars (11453246176-w)) <
      Fintype.card (Vars 11453246176) + ∑ x, ((32-r x)*(32-r x+1)/2)*399999967 := by
  classical
  have localBound (x : I) : 528*399999967 ≤
      ((32-r x)*(32-r x+1)/2)*399999967 + (31*r x+1)*399999967 := by
    have h := hr x
    interval_cases h' : r x <;> decide
  have h := sum_le_sum (s := (univ : Finset I)) (fun x _ => localBound x)
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul, ← sum_mul,
    ← mul_sum, hn] at h
  rw [hn, source_card, ← sum_mul]
  have hw := multiplier_card w h₀ h₁
  rcases hcharge with hcharge | ⟨hweight, hcharge⟩ <;> omega

#print axioms dimension_surplus
end ArkLib.ProximityGap.Frontier.SecondPrimeCubicWindowCount
