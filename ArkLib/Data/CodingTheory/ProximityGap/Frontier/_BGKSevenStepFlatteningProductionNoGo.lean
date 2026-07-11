/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Seven-step L2 flattening at the production coefficient

This file audits additive-combinatorial and entropy routes to the remaining depth-seven
injective target from `_BGKDepthSevenInjectiveVarianceEquivalence`.  If `a_y` is the number of
seven-subsets of the production subgroup with sum `y`, put

`N = n.descFactorial 7 = 7! * C(n,7)` and `p_y = 7! * a_y / N`.

The coefficient-`126871` target is exactly the chi-square estimate

`q * sum_y (p_y - 1/q)^2 <= 126871 * q * n^7 / N^2`.

Thus the injective seven-step law must be extraordinarily flat: at
`n=2^30`, `q=n*(2^128+192)+1`, its allowed chi-square divergence is strictly between
`2^-36` and `2^-35`.  Equivalently, a six-transition trajectory-flattening proof starting from
the one-step `1/n` scale needs a geometric contraction constant `c/n` with

`7^6 = 117649 < 126871 < 262144 = 8^6`.

So every uniform-step proof needs a little more than **27 L2 bits per convolution**.  This is a
useful positive socket: a centered, trajectory-specific flattening theorem with six normalized
contraction constants whose product is at most `126871` closes the injective lane.  It must act on
the signed/DC-subtracted profile; a positive raw-energy inverse theorem cannot see this window.

The exact production arithmetic below rules out the standard substitutes.

* **Uncentered BSG.**  At the target boundary the allowed non-DC mass is less than `2^-35` of
  the injective DC mass.  The natural uncentered higher-energy parameter remains the subgroup
  index `m`; already a linear `1/K` extraction loses between 98 and 99 bits relative to `n`, so
  its promised subset size is below one.  A viable inverse theorem must therefore be centered.
* **Shifted-subgroup intersections.**  Granting the classical one-shift scale
  `4*n^(2/3)` gives `2^22`.  Even granting this favorable nonzero-fibre cap as a
  flattening input, it saves only eight bits from the trivial fibre size `n=2^30`, whereas the
  trajectory needs more than 27 bits per step: an exact 19-bit one-step gap.  Its normalized
  atom scale is between `2^155` and `2^156` copies of the coefficient-`126871` excess scale.
* **Sumset covering.**  Hart's theorem `6G superset F_p^*` assumes
  `|G| > p^(11/23+epsilon)`.  Production lies on the opposite side even of the epsilon-free
  gate: the powered inequality is reversed by more than 1048 bits.  Moreover, support growth
  alone has the wrong logical direction for an L2 upper bound.

The conclusion is a sharp method-class no-go, not a disproof of the conjecture.  The remaining
additive-combinatorial socket is a **centered weighted flattening lemma** for the actual six-step
orbit trajectory (or an equivalent joint seventh-order constraint), not ordinary positive BSG,
sumset size, or a termwise shifted-intersection estimate.

Primary references:

* Shkredov--Vyugin, *On additive shifts of multiplicative subgroups*, arXiv:1102.1172.
* Shkredov--Solodkova--Vyugin, *Intersections of multiplicative subgroups and Heilbronn's
  exponential sum*, arXiv:1302.3839.
* Hart, *A note on sumsets of subgroups in `Z_p^*`*, arXiv:1303.2729.
* Bourgain--Katz--Tao, *A sum-product estimate in finite fields, and applications*,
  arXiv:math/0301343.

Issue #466.
-/

set_option autoImplicit false
set_option exponentiation.threshold 2048

open Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKSevenStepFlatteningProductionNoGo

/-! ## Collision probability and centered L2 -/

/-- Collision probability of a real-valued mass profile. -/
noncomputable def collisionProbability {Omega : Type*} [Fintype Omega]
    (mu : Omega -> Real) : Real :=
  ∑ x, (mu x) ^ 2

/-- Squared L2 distance from the uniform law. -/
noncomputable def centeredL2 {Omega : Type*} [Fintype Omega]
    (mu : Omega -> Real) : Real :=
  ∑ x, (mu x - (Fintype.card Omega : Real)⁻¹) ^ 2

/-- Exact collision/centered-L2 identity.  This is the algebra behind the Renyi-2 translation:
`collision(mu) = 1/q + ||mu-uniform||_2^2`. -/
theorem centeredL2_eq_collisionProbability_sub_uniform
    {Omega : Type*} [Fintype Omega] [Nonempty Omega] (mu : Omega -> Real)
    (hmass : ∑ x, mu x = 1) :
    centeredL2 mu = collisionProbability mu - (Fintype.card Omega : Real)⁻¹ := by
  classical
  have hq : (Fintype.card Omega : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Omega ≠ 0)
  unfold centeredL2 collisionProbability
  have hpoint : ∀ x, (mu x - (Fintype.card Omega : Real)⁻¹) ^ 2 =
      (mu x) ^ 2 - (2 * (Fintype.card Omega : Real)⁻¹) * mu x +
        ((Fintype.card Omega : Real)⁻¹) ^ 2 := by
    intro x
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hmass]
  field_simp [hq]
  ring

/-! ## Exact production cell and injective chi-square window -/

def productionN : Nat := 2 ^ 30

def productionM : Nat := 2 ^ 128 + 192

def productionQ : Nat := productionN * productionM + 1

/-- Total mass of ordered injective seven-tuples. -/
def productionInjectiveMass : Nat := productionN.descFactorial 7

def injectiveCoefficient : Nat := 126871

/-- The field size is the expected 159-bit production prime candidate. -/
theorem productionQ_bit_window :
    2 ^ 158 < productionQ ∧ productionQ < 2 ^ 159 := by
  norm_num [productionQ, productionM, productionN]

/-- The exact normalized injective chi-square allowance
`126871*q*n^7/(n)_7^2` lies strictly between `2^-36` and `2^-35`.

The division-free inequalities are stated in the direction that avoids any rounding. -/
theorem injective_chiSquare_strict_35_36_bit_window :
    2 ^ 35 * (injectiveCoefficient * productionQ * productionN ^ 7) <
        productionInjectiveMass ^ 2 ∧
      productionInjectiveMass ^ 2 <
        2 ^ 36 * (injectiveCoefficient * productionQ * productionN ^ 7) := by
  norm_num [injectiveCoefficient, productionInjectiveMass, productionQ, productionM,
    productionN, Nat.descFactorial_succ, Nat.descFactorial_zero]

/-- At the target boundary, the complete raw injective energy is within a relative `2^-35`
of its DC term.  Hence an uncentered positive-energy inverse theorem cannot resolve the target
unless its constants see a 35-bit relative perturbation. -/
theorem raw_injective_energy_target_below_one_plus_two_neg35 :
    2 ^ 35 *
        (productionInjectiveMass ^ 2 +
          injectiveCoefficient * productionQ * productionN ^ 7) <
      (2 ^ 35 + 1) * productionInjectiveMass ^ 2 := by
  have h := injective_chiSquare_strict_35_36_bit_window.1
  omega

/-! ## Six-step trajectory-flattening threshold -/

/-- The sixth root of the exact coefficient lies strictly between the consecutive integers
seven and eight. -/
theorem six_step_integer_contraction_window :
    7 ^ 6 < injectiveCoefficient ∧ injectiveCoefficient < 8 ^ 6 := by
  norm_num [injectiveCoefficient]

/-- Six uniform contractions with numerator seven fit inside the injective allocation, while
numerator eight does not.  This is the exact integer form of the `>27` L2-bit-per-step socket. -/
theorem seven_suffices_eight_overshoots :
    7 ^ 6 = 117649 ∧ 8 ^ 6 = 262144 ∧
      117649 < injectiveCoefficient ∧ injectiveCoefficient < 262144 := by
  norm_num [injectiveCoefficient]

/-- The same consecutive-integer window remains exact after restoring the falling-factorial
normalization of the injective law.  If six trajectory contractions have common scale `c/n`,
then `c=7` is sufficient at production and `c=8` overshoots the exact normalized target. -/
theorem exact_injective_uniform_contraction_window :
    7 ^ 6 * productionInjectiveMass ^ 2 <
        injectiveCoefficient * productionN ^ 14 ∧
      injectiveCoefficient * productionN ^ 14 <
        8 ^ 6 * productionInjectiveMass ^ 2 := by
  norm_num [injectiveCoefficient, productionInjectiveMass, productionN,
    Nat.descFactorial_succ, Nat.descFactorial_zero]

/-- At production, the comparison contraction `8/n` is exactly `2^-27`.  Since
`126871 < 8^6`, a uniform six-step contraction proof must do strictly better than this boundary. -/
theorem comparison_contraction_is_two_neg27 :
    8 * 2 ^ 27 = productionN := by
  norm_num [productionN]

/-! ## Ordinary BSG loses the production scale before extracting a point -/

/-- The subgroup index is between `2^98` and `2^99` copies of the subgroup size.  Thus even a
best-case inverse theorem extracting an `n/K` fraction with `K` at the raw DC parameter `m`
has a 98--99 bit size loss. -/
theorem bsg_raw_parameter_loses_98_99_bits :
    2 ^ 98 * productionN < productionM ∧
      productionM < 2 ^ 99 * productionN := by
  norm_num [productionM, productionN]

/-- In particular the integer lower-bound scale `n/m` is already zero. -/
theorem bsg_linear_fraction_below_one : productionN / productionM = 0 := by
  norm_num [productionM, productionN]

/-! ## Granted shifted-subgroup intersection scale is 19 contraction bits short -/

/-- Arithmetic proxy for the *granted* classical one-shift scale `4*n^(2/3)` at `n=2^30`.
Here `n^(1/3)=2^10`, so that scale is exactly `2^22`.  This definition does not import or assert
the analytic intersection theorem; the following lemmas only audit what its stated cap could buy. -/
def shiftedOneIntersectionCap : Nat := 4 * (2 ^ 10) ^ 2

theorem shiftedOneIntersectionCap_eq : shiftedOneIntersectionCap = 2 ^ 22 := by
  norm_num [shiftedOneIntersectionCap]

/-- Relative to the trivial fibre size `n`, the shifted-intersection cap supplies only eight
bits of pointwise flattening. -/
theorem shifted_cap_saves_exactly_eight_bits :
    2 ^ 8 * shiftedOneIntersectionCap = productionN := by
  norm_num [shiftedOneIntersectionCap, productionN]

/-- The required comparison contraction numerator is `8`, whereas the shifted fibre cap has
numerator `2^22`; their exact gap is `2^19`. -/
theorem shifted_cap_misses_step_budget_by_19_bits :
    shiftedOneIntersectionCap = 2 ^ 19 * 8 := by
  norm_num [shiftedOneIntersectionCap]

/-- Even the favorable normalized nonzero-pair atom cap `2^22/n^2`, compared directly with the
depth-seven excess scale `126871/n^7`, is between `2^155` and `2^156` times too large.  This is a
scale comparison, not a lower bound on the actual atom or variance. -/
theorem shifted_cap_vs_depthSeven_excess_155_156_bits :
    2 ^ 155 * injectiveCoefficient < shiftedOneIntersectionCap * productionN ^ 5 ∧
      shiftedOneIntersectionCap * productionN ^ 5 < 2 ^ 156 * injectiveCoefficient := by
  norm_num [injectiveCoefficient, shiftedOneIntersectionCap, productionN]

/-! ## Fixed-depth sumset covering is far outside the production density -/

/-- Hart's sixfold covering hypothesis starts (even before its `epsilon`) at
`n > q^(11/23)`, equivalently `n^23 > q^11`.  Production satisfies the reverse powered
inequality with more than 1048 bits of slack. -/
theorem hart_sixfold_density_gate_reversed_by_1048_bits :
    2 ^ 1048 * productionN ^ 23 < productionQ ^ 11 := by
  norm_num [productionQ, productionM, productionN]

/-- The corresponding exponent comparison: even the optimistic upper density exponent
`30/158` is below Hart's `11/23` threshold. -/
theorem production_density_exponent_below_hart :
    (30 : Rat) / 158 < 11 / 23 := by
  norm_num

#print axioms centeredL2_eq_collisionProbability_sub_uniform
#print axioms productionQ_bit_window
#print axioms injective_chiSquare_strict_35_36_bit_window
#print axioms raw_injective_energy_target_below_one_plus_two_neg35
#print axioms six_step_integer_contraction_window
#print axioms seven_suffices_eight_overshoots
#print axioms exact_injective_uniform_contraction_window
#print axioms comparison_contraction_is_two_neg27
#print axioms bsg_raw_parameter_loses_98_99_bits
#print axioms bsg_linear_fraction_below_one
#print axioms shiftedOneIntersectionCap_eq
#print axioms shifted_cap_saves_exactly_eight_bits
#print axioms shifted_cap_misses_step_budget_by_19_bits
#print axioms shifted_cap_vs_depthSeven_excess_155_156_bits
#print axioms hart_sixfold_density_gate_reversed_by_1048_bits
#print axioms production_density_exponent_below_hart

end ArkLib.ProximityGap.Frontier.BGKSevenStepFlatteningProductionNoGo
