/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Loop 35 — unbounded exponent density is the real multiplicative danger

Loops 31--34 progressively ruled out bounded-density multiplicative attacks: bounded exponents,
bounded-density blocks, bounded sparse spikes, and a bounded number of height-linear spikes. This
file records the complementary arithmetic danger.

If the cumulative multiplicative exponent over `m` levels is at least `m*D`, and `D` is larger than a
target final polynomial degree `d`, then the product already beats `((2^m)^d)`. Thus a true
multiplicative disproof must force exponent density `D` beyond every fixed prize exponent in the
actual smooth-domain GS/proximity mechanism.

This is still not a disproof of the prize: it is the arithmetic criterion a real disproof would have
to realize. See `DISPROOF_LOG.md` (Loop35).
-/

namespace ArkLib.ProximityGap.StructureLoop35

open scoped BigOperators

/-- **Final-domain powers are powers with linear exponent.** This is the exponent accounting behind
the prize numerator: degree `D` in the final domain `2^m` is exponent `m*D` in base `2`. -/
theorem density_product_eq (D m : ℕ) :
    ((2 : ℝ) ^ m) ^ D = (2 : ℝ) ^ (m * D) := by
  rw [← pow_mul]

/-- **Arbitrary exponent products collapse to one power.** The multiplicative tower is controlled by
the cumulative exponent. -/
theorem exponent_product_eq (e : ℕ → ℕ) (m : ℕ) :
    (∏ j ∈ Finset.range m, (2 : ℝ) ^ e j) =
      (2 : ℝ) ^ (∑ j ∈ Finset.range m, e j) := by
  exact Finset.prod_pow_eq_pow_sum (Finset.range m) e (2 : ℝ)

/-- **Exponent density above degree `d` overflows final degree `d`.** If the cumulative exponent is
at least `m*D`, with `D>d`, then the product beats the degree-`d` final-domain polynomial. -/
theorem exponent_density_overflows_final_degree
    (e : ℕ → ℕ) {D d m : ℕ}
    (hm : 0 < m)
    (hd : d < D)
    (hsum : m * D ≤ ∑ j ∈ Finset.range m, e j) :
    ((2 : ℝ) ^ m) ^ d < ∏ j ∈ Finset.range m, (2 : ℝ) ^ e j := by
  rw [exponent_product_eq]
  rw [← pow_mul]
  have hExp : m * d < ∑ j ∈ Finset.range m, e j := by
    exact (Nat.mul_lt_mul_of_pos_left hd hm).trans_le hsum
  exact pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hExp

/-- **One extra unit of density already overflows.** Density at least `d+1` beats final degree `d`. -/
theorem density_one_more_overflows_final_degree
    (e : ℕ → ℕ) {d m : ℕ}
    (hm : 0 < m)
    (hsum : m * (d + 1) ≤ ∑ j ∈ Finset.range m, e j) :
    ((2 : ℝ) ^ m) ^ d < ∏ j ∈ Finset.range m, (2 : ℝ) ^ e j := by
  exact exponent_density_overflows_final_degree e hm (Nat.lt_succ_self d) hsum

/-- **The spike-density form of the overflow criterion.** If the effective spike density `K*h`
exceeds final degree `d`, and the cumulative exponent realizes at least `m*(K*h)`, the product
overflows degree `d`. Loop 34 says bounded `K*h` is still just a polynomial degree; this theorem says
why unbounded `K*h` would be dangerous if the GS process actually realized it. -/
theorem linear_spike_density_overflows_final_degree
    (e : ℕ → ℕ) {K h d m : ℕ}
    (hm : 0 < m)
    (hd : d < K * h)
    (hsum : m * (K * h) ≤ ∑ j ∈ Finset.range m, e j) :
    ((2 : ℝ) ^ m) ^ d < ∏ j ∈ Finset.range m, (2 : ℝ) ^ e j := by
  exact exponent_density_overflows_final_degree e hm hd hsum

end ArkLib.ProximityGap.StructureLoop35

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop35.density_product_eq
#print axioms ArkLib.ProximityGap.StructureLoop35.exponent_product_eq
#print axioms ArkLib.ProximityGap.StructureLoop35.exponent_density_overflows_final_degree
#print axioms ArkLib.ProximityGap.StructureLoop35.density_one_more_overflows_final_degree
#print axioms ArkLib.ProximityGap.StructureLoop35.linear_spike_density_overflows_final_degree
