/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Loop 32 — block grouping cannot hide multiplicative exponent growth

Loop 31 reduced multiplicative-factor attacks to the cumulative exponent `∑ e_j`. This file closes
one obvious loophole: grouping levels into irregular blocks. If a block of width `w_i` contributes a
multiplicative factor `2^(b_i)` and each block exponent is bounded by `w_i * c`, then the whole
blocked product is still bounded by the final-domain polynomial `((2^m)^c)`, where
`m = ∑ w_i`.

Thus a spiky or blocked multiplicative disproof still has to produce block exponents whose **total
density** exceeds every constant. Repackaging bounded-density work into blocks does not create a
counterexample. See `DISPROOF_LOG.md` (Loop32).
-/

namespace ArkLib.ProximityGap.StructureLoop32

open scoped BigOperators

/-- **Block exponent products collapse to one power.** Grouping fold levels into blocks changes the
indexing, not the fact that multiplicative exponents add. -/
theorem block_exponent_product_eq (b : ℕ → ℕ) (r : ℕ) :
    (∏ i ∈ Finset.range r, (2 : ℝ) ^ b i) =
      (2 : ℝ) ^ (∑ i ∈ Finset.range r, b i) := by
  exact Finset.prod_pow_eq_pow_sum (Finset.range r) b (2 : ℝ)

/-- **Bounded block density is prize-safe.** If the block widths sum to final depth `m`, and every
block exponent is at most `c` times its width, then the grouped multiplicative product is bounded by
the final-domain degree-`c` polynomial. -/
theorem block_exponent_product_le_domain_pow
    (width b : ℕ → ℕ) {r c m : ℕ}
    (hm : ∑ i ∈ Finset.range r, width i = m)
    (hblock : ∀ i, i < r → b i ≤ width i * c) :
    (∏ i ∈ Finset.range r, (2 : ℝ) ^ b i) ≤ ((2 : ℝ) ^ m) ^ c := by
  have hsum : ∑ i ∈ Finset.range r, b i ≤ m * c := by
    calc
      ∑ i ∈ Finset.range r, b i ≤ ∑ i ∈ Finset.range r, width i * c := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact hblock i (Finset.mem_range.mp hi)
      _ = (∑ i ∈ Finset.range r, width i) * c := by
        rw [Finset.sum_mul]
      _ = m * c := by rw [hm]
  rw [block_exponent_product_eq]
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hsum

/-- **Only total block exponent overflow matters.** If the sum of block exponents beats `m*d`, then
the grouped multiplicative product is larger than the final-domain degree-`d` polynomial. -/
theorem block_exponent_product_overflows_of_sum
    (b : ℕ → ℕ) {r d m : ℕ}
    (hsum : m * d < ∑ i ∈ Finset.range r, b i) :
    ((2 : ℝ) ^ m) ^ d < ∏ i ∈ Finset.range r, (2 : ℝ) ^ b i := by
  rw [block_exponent_product_eq]
  rw [← pow_mul]
  exact pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hsum

end ArkLib.ProximityGap.StructureLoop32

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop32.block_exponent_product_eq
#print axioms ArkLib.ProximityGap.StructureLoop32.block_exponent_product_le_domain_pow
#print axioms ArkLib.ProximityGap.StructureLoop32.block_exponent_product_overflows_of_sum
