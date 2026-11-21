/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Tactic

/-! # Effective jet dimensions after subtracting all cubic multiples

The scalar-degree window includes every value degree permitted by the weight.
The count below retains its quadratic dependence on the unknown weight of the
cubic and proves the strict dimension surplus across the entire weight range.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SecondPrimeUnrestrictedJetBudget

/-- Coordinate slots for the first m value degrees within a weight cutoff. -/
def slots (v d : ℤ) (m : ℕ) : ℤ := ∑ j ∈ Finset.range m, (v - j*d)

theorem twice_slots (v d : ℤ) (m : ℕ) :
    2*slots v d m = (m : ℤ)*(2*v-d*(m-1)) := by
  induction m with
  | zero => simp [slots]
  | succ m ih =>
    simp only [slots, Finset.sum_range_succ, Nat.cast_succ] at *
    linarith only [ih]

private theorem weighted_slots (v d : ℤ) (m : ℕ) :
    2*d*slots v d m = v^2 + d*v + ((m : ℤ)*d-v)*(v-((m : ℤ)-1)*d) := by
  linear_combination d * twice_slots v d m

/-- The unrestricted slot difference pays at least the difference of the
continuous triangular areas. The endpoint terms are controlled uniformly. -/
theorem slot_difference_lower (u w d : ℤ) (m k : ℕ) (hd : 0 < d) (hw : d ≤ w)
    (hm : ((m : ℤ)-1)*d ≤ u) (hm' : u ≤ (m : ℤ)*d)
    (hk : ((k : ℤ)-1)*d ≤ u-w) (hk' : u-w ≤ (k : ℤ)*d) :
    2*u*w-w^2 ≤ 2*d*(slots u d m - slots (u-w) d k) := by
  have hm0 := mul_nonneg (sub_nonneg.mpr hm') (sub_nonneg.mpr hm)
  have hka : (k : ℤ)*d-(u-w) ≤ d := by linarith
  have hkb : u-w-((k : ℤ)-1)*d ≤ d := by linarith
  have hik := mul_le_mul hka hkb (sub_nonneg.mpr hk) hd.le
  nlinarith only [weighted_slots u d m, weighted_slots (u-w) d k, hm0, hik,
    mul_le_mul_of_nonneg_left hw hd.le]

/-- Rank loss of the two ordinary first polars costs at most 266 orders. -/
theorem gcd_defect (w : ℤ) (hw : w ≤ 290805098) :
    (10*w-16*67108863-6)*195 < 267*(1342177249-164-195) := by omega

/-- The raw resultant estimate and the ordinary polar gcd imply the cubic
multiplicity bound used in the unrestricted jet calculation. -/
theorem received_bound (w g r : ℤ) (hg : 2*(w-67108863)-266 ≤ g)
    (hr : 3*r ≤ 2*1073741824 + (16*w-27*67108863) - 2*g + 4*(w-3*67108863)) :
    3*r ≤ 2*1073741824 + 16*w - 35*67108863 + 532 := by omega

/-- The remaining auxiliary dimension is strictly positive at every possible
weight of the component, even after deducting all its polynomial multiples. -/
theorem jet_surplus (w r : ℤ) (hl : 201326589 ≤ w) (hu : w ≤ 290805098)
    (hr : 3*r ≤ 2*1073741824 + 16*w - 35*67108863 + 532) :
    (2*67108863)*(170*983077772391 +
        (400000001-34)*(31*r+1073741824)+34*1073741824*528) <
      400000001*(2*(32*357913943)*w-w^2) := by
  have hp := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)
  nlinarith only [hp,hl,hu,hr]

/-- Full index count and resultant cutoff checked at the production parameters. -/
theorem slot_and_resultant_bounds :
    slots (32*357913943) 67108863 171 = 983077772391 ∧
    170*67108863 < (32*357913943 : ℤ) ∧ (32*357913943 : ℤ) ≤ 171*67108863 ∧
    (3*400000000+34*170 : ℕ) < 1342177249 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  have h := twice_slots (32*357913943) 67108863 171
  omega

#print axioms slot_difference_lower
#print axioms received_bound
#print axioms jet_surplus
#print axioms slot_and_resultant_bounds

end ArkLib.ProximityGap.Frontier.SecondPrimeUnrestrictedJetBudget
