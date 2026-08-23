/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Loop 31 — variable multiplicative exponents: only the total exponent matters

Loop 30 showed that local polynomial factors `(2^j)^c`, multiplied over fold levels, become dangerous
because their exponents sum to a quadratic-in-depth quantity. This file records the fully variable
version. For arbitrary nonnegative level exponents `e_j`,

    ∏_{j<m} 2^(e_j) = 2^(∑_{j<m} e_j).

So multiplicative branching is prize-safe whenever the total exponent is `O(m)`, and it can beat a
fixed final-domain polynomial only when the total exponent beats `m*d`. This shoots down attempted
disproofs based on uneven or adaptive level factors unless they prove a **superlinear cumulative
exponent** inside the actual GS/proximity mechanism. See `DISPROOF_LOG.md` (Loop31).
-/

namespace ArkLib.ProximityGap.StructureLoop31

open scoped BigOperators

/-- **Variable exponent products collapse to one power.** The cumulative multiplicative contribution
of factors `2^(e_j)` is exactly controlled by the sum of the exponents. -/
theorem variable_exponent_product_eq (e : ℕ → ℕ) (m : ℕ) :
    (∏ j ∈ Finset.range m, (2 : ℝ) ^ e j) =
      (2 : ℝ) ^ (∑ j ∈ Finset.range m, e j) := by
  exact Finset.prod_pow_eq_pow_sum (Finset.range m) e (2 : ℝ)

/-- **Linear cumulative exponent is prize-safe.** If the total variable exponent through depth `m`
is at most `m*c`, then the product of multiplicative factors is bounded by the final-domain
degree-`c` polynomial `((2^m)^c)`. -/
theorem variable_exponent_product_le_domain_pow
    (e : ℕ → ℕ) {c m : ℕ}
    (hsum : ∑ j ∈ Finset.range m, e j ≤ m * c) :
    (∏ j ∈ Finset.range m, (2 : ℝ) ^ e j) ≤ ((2 : ℝ) ^ m) ^ c := by
  rw [variable_exponent_product_eq]
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hsum

/-- **Uniformly bounded level exponents are prize-safe.** A bounded per-level exponent gives a
linear total exponent, hence only a fixed-degree polynomial in the final smooth-domain size. -/
theorem variable_exponent_product_le_domain_pow_of_pointwise
    (e : ℕ → ℕ) {c m : ℕ} (he : ∀ j, j < m → e j ≤ c) :
    (∏ j ∈ Finset.range m, (2 : ℝ) ^ e j) ≤ ((2 : ℝ) ^ m) ^ c := by
  refine variable_exponent_product_le_domain_pow e ?_
  calc
    ∑ j ∈ Finset.range m, e j ≤ ∑ _j ∈ Finset.range m, c := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact he j (Finset.mem_range.mp hj)
    _ = m * c := by simp

/-- **Superlinear cumulative exponent overflows a fixed final degree.** If the total exponent beats
`m*d`, then the variable multiplicative product is already larger than the degree-`d` polynomial in
the final smooth-domain size. -/
theorem variable_exponent_product_overflows_of_sum
    (e : ℕ → ℕ) {d m : ℕ}
    (hsum : m * d < ∑ j ∈ Finset.range m, e j) :
    ((2 : ℝ) ^ m) ^ d < ∏ j ∈ Finset.range m, (2 : ℝ) ^ e j := by
  rw [variable_exponent_product_eq]
  rw [← pow_mul]
  exact pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hsum

end ArkLib.ProximityGap.StructureLoop31

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop31.variable_exponent_product_eq
#print axioms ArkLib.ProximityGap.StructureLoop31.variable_exponent_product_le_domain_pow
#print axioms ArkLib.ProximityGap.StructureLoop31.variable_exponent_product_le_domain_pow_of_pointwise
#print axioms ArkLib.ProximityGap.StructureLoop31.variable_exponent_product_overflows_of_sum
