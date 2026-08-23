/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Loop 30 — local polynomial multiplicative factors are dangerous only as a product

Loops 28 and 29 separated multiplicative and additive fold accounting. This file records the
remaining arithmetic danger: if every fold level `j` contributed a **multiplicative** local-polynomial
factor `(2^j)^c`, then the cumulative product is

    ∏_{j<m} (2^j)^c = 2^(∑_{j<m} j*c).

That exponent can beat any fixed final-domain polynomial exponent `m*d` once the summed local
exponents are large enough. This is a real counterexample *shape*, but only a conditional arithmetic
one: it does not prove that actual faithful GS proximity lists branch multiplicatively by such local
polynomial factors at each fold. See `DISPROOF_LOG.md` (Loop30).
-/

namespace ArkLib.ProximityGap.StructureLoop30

open scoped BigOperators

/-- **A product of local polynomial factors collapses to one power with summed local exponents.**
If fold level `j` contributes `(2^j)^c`, the cumulative multiplicative factor through `m` levels is
`2^(∑_{j<m} j*c)`. -/
theorem local_polynomial_product_eq (c m : ℕ) :
    (∏ j ∈ Finset.range m, (((2 : ℝ) ^ j) ^ c)) =
      (2 : ℝ) ^ (∑ j ∈ Finset.range m, j * c) := by
  calc
    (∏ j ∈ Finset.range m, (((2 : ℝ) ^ j) ^ c))
        = ∏ j ∈ Finset.range m, (2 : ℝ) ^ (j * c) := by
          simp [pow_mul]
    _ = (2 : ℝ) ^ (∑ j ∈ Finset.range m, j * c) := by
          exact Finset.prod_pow_eq_pow_sum (Finset.range m) (fun j => j * c) (2 : ℝ)

/-- **Conditional overflow criterion.** If the summed local exponents beat the final-domain
polynomial exponent `m*d`, then the local-polynomial multiplicative product is larger than the
degree-`d` polynomial in the final smooth-domain size `2^m`. A true disproof must realize such a
product inside the actual GS/proximity mechanism, not merely as standalone arithmetic. -/
theorem local_polynomial_product_overflows_of_exponent
    {c d m : ℕ}
    (hExp : m * d < ∑ j ∈ Finset.range m, j * c) :
    ((2 : ℝ) ^ m) ^ d <
      ∏ j ∈ Finset.range m, (((2 : ℝ) ^ j) ^ c) := by
  rw [local_polynomial_product_eq]
  rw [← pow_mul]
  exact pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hExp

/-- **Positive local degree eventually overflows any fixed final degree.** At depth `2*d+3`, even
the triangular sum of bare level indices already beats `m*d`; multiplying each level by any positive
local degree `c` preserves that strict overflow. -/
theorem local_exponent_sum_overflows_at_depth (c d : ℕ) (hc : 0 < c) :
    (2 * d + 3) * d < ∑ j ∈ Finset.range (2 * d + 3), j * c := by
  have hbase : (2 * d + 3) * d < ∑ j ∈ Finset.range (2 * d + 3), j := by
    have htri := Finset.sum_range_id_mul_two (2 * d + 3)
    have hsub : 2 * d + 3 - 1 = 2 * d + 2 := by omega
    rw [hsub] at htri
    nlinarith
  have hmono : (∑ j ∈ Finset.range (2 * d + 3), j) ≤
      ∑ j ∈ Finset.range (2 * d + 3), j * c := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact Nat.le_mul_of_pos_right (m := c) j hc
  exact lt_of_lt_of_le hbase hmono

/-- **Concrete local-product overflow.** If each level has a positive-degree local-polynomial
multiplicative factor `(2^j)^c`, then by depth `2*d+3` the cumulative product is already larger than
the final-domain degree-`d` polynomial. This remains only an arithmetic obstruction until such
multiplicative local branching is realized by the actual GS/proximity process. -/
theorem local_polynomial_product_overflows_at_depth {c d : ℕ} (hc : 0 < c) :
    ((2 : ℝ) ^ (2 * d + 3)) ^ d <
      ∏ j ∈ Finset.range (2 * d + 3), (((2 : ℝ) ^ j) ^ c) := by
  exact local_polynomial_product_overflows_of_exponent
    (local_exponent_sum_overflows_at_depth c d hc)

end ArkLib.ProximityGap.StructureLoop30

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop30.local_polynomial_product_eq
#print axioms ArkLib.ProximityGap.StructureLoop30.local_polynomial_product_overflows_of_exponent
#print axioms ArkLib.ProximityGap.StructureLoop30.local_exponent_sum_overflows_at_depth
#print axioms ArkLib.ProximityGap.StructureLoop30.local_polynomial_product_overflows_at_depth
