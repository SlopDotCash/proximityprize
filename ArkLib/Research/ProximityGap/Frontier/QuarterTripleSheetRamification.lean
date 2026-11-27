/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-!
# Third fixed-point moment of a quarter-rate split pencil

For an inertia power fixing `f` sheets, the number of ordered distinct triples fixed
is `f*(f-1)*(f-2)`. Its discrete supporting line gives a genus bound linear in the
orbifold excess. Combining it with the seven-dimensional cube Wronskian on the
ordered-triple curve yields the numerical bounds below. The function-field and
Wronskian arguments are given in the accompanying research note.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.QuarterTripleSheetRamification

open Finset

/-- The affine function agreeing with the falling cubic at two successive integers lies
below the falling cubic at every nonnegative integer. -/
theorem falling_three_tangent (f b : ℤ) (hf : 0 ≤ f) (hb : 1 ≤ b) :
    3*b*(b-1)*f - 2*b*(b-1)*(b+1) ≤ f*(f-1)*(f-2) := by
  have hp : 0 ≤ (f-b)*(f-b-1) := by
    by_cases h : b < f
    · exact mul_nonneg (by omega) (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have h := mul_nonneg hp (show 0 ≤ f + 2*b - 2 by omega)
  nlinarith only [h]

/-- Summing the discrete tangent against the nonidentity-power weights in
Riemann–Hurwitz bounds the third fixed-point moment from the first one. -/
theorem weighted_falling_three {ι : Type*} (S : Finset ι) (w : ι → ℚ) (F : ι → ℤ)
    {b : ℤ} (hb : 1 ≤ b) (hw : ∀ i ∈ S, 0 ≤ w i) (hF : ∀ i ∈ S, 0 ≤ F i)
    {m E : ℚ} (h₀ : ∑ i ∈ S, w i = E+2) (h₁ : ∑ i ∈ S, w i*(F i : ℚ) = m*E+2) :
    3*(b : ℚ)*(b-1)*(m*E+2) - 2*b*(b-1)*(b+1)*(E+2) ≤
      ∑ i ∈ S, w i*((F i : ℚ)*(F i-1)*(F i-2)) := by
  let B : ℚ := 3*(b : ℚ)*(b-1)
  let C : ℚ := 2*(b : ℚ)*(b-1)*(b+1)
  change B*(m*E+2) - C*(E+2) ≤ _
  rw [← h₀, ← h₁, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have ht : B*(F i : ℚ)-C ≤ (F i : ℚ)*(F i-1)*(F i-2) := by
    dsimp [B, C]
    exact_mod_cast falling_three_tangent (F i) b (hF i hi) hb
  calc B*(w i*(F i : ℚ)) - C*w i = w i*(B*(F i : ℚ)-C) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left ht (hw i hi)

/-- Number of ordered choices for the remaining two sheets once the first is fixed. -/
def pairChoices (m : ℚ) : ℚ := (m-1)*(m-2)

/-- Combining the ordered-triple Wronskian with the discrete genus bound at one tangent. -/
theorem stage_cut {m a n₀ b E G : ℚ}
    (hWr : 21*m*a ≤ 3*n₀*a + 21*(G+6*a))
    (hgen : G ≤ m*a*E - 3*b*(b-1)*(m*E+2) + 2*b*(b-1)*(b+1)*(E+2)) :
    (21*m-3*n₀-126)*a + 126*b*(b-1) - 84*b*(b-1)*(b+1) ≤
      21*(m*a-3*m*b*(b-1)+2*b*(b-1)*(b+1))*E := by
  linarith only [hWr, hgen] <;> ring_nf at *

/-- The weaker of the two outer-degree-one stage floors. -/
def uniformFloor : ℚ := 45663621513021794134939 / 103042957874781541548323

/-- Both possible outer-degree-one stages satisfy the uniform floor. -/
theorem outer_one_floor {m n₀ b E G : ℚ}
    (hstage : (m=134217727 ∧ n₀=536870912 ∧ b=24345100) ∨
      (m=268435454 ∧ n₀=1073741824 ∧ b=48690201))
    (hWr : 21*m*pairChoices m ≤ 3*n₀*pairChoices m + 21*(G+6*pairChoices m))
    (hgen : G ≤ m*pairChoices m*E - 3*b*(b-1)*(m*E+2) + 2*b*(b-1)*(b+1)*(E+2)) :
    uniformFloor ≤ E := by
  have h := stage_cut hWr hgen
  rcases hstage with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    norm_num [pairChoices, uniformFloor] at h ⊢ <;> linarith

/-- The established ordered-pair floor after an outer quadratic also gives the uniform floor. -/
theorem outer_two_floor {E E_R : ℚ} (hE : 268435426 / 268435465 ≤ E) (hcharge : E ≤ 2*E_R) :
    uniformFloor ≤ E_R := by
  unfold uniformFloor
  linarith

/-- Explicit characteristic budget for the cube Wronskian on every component of the
degree-at-most-eight pullback. -/
theorem characteristic_budget :
    3*(2:ℕ)^30*8*268435454^2 < 365375409332725729550921208179070755120141565953 := by
  decide

/-- For a three-branch signature the floor excludes the indicated ranges on the last order.
The first two inequalities exclude all last orders for the two indicated initial pairs. -/
theorem signature_cuts :
    (1-(1:ℚ)/2-1/17 < uniformFloor) ∧ (1-(1:ℚ)/3-1/4 < uniformFloor) ∧
    (1-(1:ℚ)/2-1/18-1/773 < uniformFloor) ∧
    (1-(1:ℚ)/2-1/19-1/237 < uniformFloor) ∧
    (1-(1:ℚ)/3-1/5-1/42 < uniformFloor) ∧
    (1-(1:ℚ)/4-1/4-1/17 < uniformFloor) ∧
    ((4431513:ℚ)/10000000 < uniformFloor) := by
  norm_num [uniformFloor]

/-- On the one or two fibers of an inertia involution over the outer map, the normalized
third falling moment restricts the mean number of fixed primitive sheets. -/
theorem inertia_fixed_mean {m b fixedMean thirdMean : ℚ}
    (hstage : (m=134217727 ∧ b=70163658) ∨ (m=268435454 ∧ b=140327317))
    (hthird : 7*thirdMean ≤ pairChoices m*(m+100))
    (htangent : 3*b*(b-1)*fixedMean - 2*b*(b-1)*(b+1) ≤ thirdMean) :
    25000*fixedMean < 13069*m := by
  rcases hstage with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [pairChoices] at hthird htangent ⊢ <;> linarith

/-- A production inertia involution moves an even number of sheets. -/
theorem inertia_moved {fixed transpositions : ℕ}
    (hsize : fixed + 2*transpositions = 268435454)
    (hcut : 25000*fixed < 13069*268435454) : 128108138 ≤ 2*transpositions := by
  omega

/-- The same argument for every inertia order, using the weakest allowable third-moment cap. -/
theorem inertia_any_fixed_mean {m b fixedMean thirdMean : ℚ}
    (hstage : (m=134217727 ∧ b=111377896) ∨ (m=268435454 ∧ b=222755792))
    (hthird : 7*thirdMean ≤ pairChoices m*(4*m+50))
    (htangent : 3*b*(b-1)*fixedMean - 2*b*(b-1)*(b+1) ≤ thirdMean) :
    100000*fixedMean < 82983*m := by
  rcases hstage with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [pairChoices] at hthird htangent ⊢ <;> linarith

/-- The cap specialized to order three. -/
theorem inertia_three_fixed_mean {m b fixedMean thirdMean : ℚ}
    (hstage : (m=134217727 ∧ b=95227477) ∨ (m=268435454 ∧ b=190454954))
    (hthird : 14*thirdMean ≤ pairChoices m*(5*m+150))
    (htangent : 3*b*(b-1)*fixedMean - 2*b*(b-1)*(b+1) ≤ thirdMean) :
    2000*fixedMean < 1419*m := by
  rcases hstage with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [pairChoices] at hthird htangent ⊢ <;> linarith

/-- Numbers of moved sheets for unrestricted inertia and for order three, respectively. -/
theorem inertia_other_support {fixed moved : ℕ} (hsize : fixed+moved=268435454) :
    (100000*fixed < 82983*268435454 → 45679662 ≤ moved) ∧
    (2000*fixed < 1419*268435454 → 77980500 ≤ moved) := by omega

#print axioms weighted_falling_three
#print axioms stage_cut
#print axioms outer_one_floor
#print axioms outer_two_floor
#print axioms signature_cuts
#print axioms inertia_fixed_mean
#print axioms inertia_moved
#print axioms inertia_any_fixed_mean
#print axioms inertia_three_fixed_mean

end ArkLib.ProximityGap.Frontier.QuarterTripleSheetRamification
