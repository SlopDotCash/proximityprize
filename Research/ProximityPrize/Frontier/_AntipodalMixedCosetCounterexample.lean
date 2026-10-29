/-
Copyright (c) 2026 Lucas. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Lucas
-/
import Research.ProximityPrize.Frontier._AntipodalEvenOddDescent
import Research.ProximityPrize.Frontier._AvX_PrimitiveTwoPowRootHalfPowerEq
import Research.ProximityPrize.Frontier._PrizeShapePrimeP30
import Research.ProximityPrize.Frontier._PrizeShapePrimeP30Second

/-!
# Isolated agreement roots need not occupy one half-subgroup coset

This formalizes Hardyzyt's mixed-coset construction from
`scripts/probes/probe_antipodal_subgroup_obstructions.py`, merged in
[PR #230](https://github.com/SlopDotCash/proximityprize/pull/230).
The construction and its mathematical obstruction are prior work; this file adds Lean proofs.

For `n = 2^30`, `k = b = 2^29`, `a = b + 2`, and an element `g` of order `n`, set
`c(X) = (g + 1) X - (g^2 + g)` and `P(X) = X^a - g^2 X^b - c(X)`.
The head exponents are even, `k ≤ b < a < n`, the head coefficient is nonzero, and
`c.natDegree = 1 < k`. Both `1` and `g` are roots; their antipodes are not roots.
Their half-order powers are respectively `1` and `-1`, so the isolated roots cannot
all lie in any one coset of `{u | u^(2^29) = 1}`.

This refutes coset confinement, not the valid `isolated_root_determined` identity in
`_AntipodalEvenOddDescent.lean`. Only two isolated agreement points are certified;
no production-radius bad scalar, root-count upper bound, or decoding threshold follows.
The second, five-root construction in the Python probe is not formalized here.

Assumptions: a field of characteristic different from two and a generator of order `2^30`.
Both concrete instances discharge these with the existing sponsor primality/order certificates.
No new axioms or residual assumptions. Check with
`scripts/pg-iterate.sh Research/ProximityPrize/Frontier/_AntipodalMixedCosetCounterexample.lean`.
-/

namespace ProximityGap.Frontier.AntipodalMixedCosetCounterexample

open Polynomial

set_option autoImplicit false

noncomputable section

variable {F : Type*} [Field F]

/-- The linear tail from Hardyzyt's mixed-coset witness. -/
def tail (g : F) : F[X] := C (g + 1) * X - C (g ^ 2 + g)

private def agreementAt (b : ℕ) (g : F) : F[X] :=
  X ^ (b + 2) - C (g ^ 2) * X ^ b - tail g

/-- The agreement polynomial, with two even high exponents at production dimension. -/
def agreement (g : F) : F[X] := agreementAt (2 ^ 29) g

private theorem agreementAt_eval (b : ℕ) (g x : F) :
    (agreementAt b g).eval x =
      x ^ (b + 2) - g ^ 2 * x ^ b - ((g + 1) * x - (g ^ 2 + g)) := by
  simp [agreementAt, tail]

/-- Evaluation exposes the original sparse-head, linear-tail construction. -/
theorem agreement_eval (g x : F) :
    (agreement g).eval x =
      x ^ (2 ^ 29 + 2) - g ^ 2 * x ^ (2 ^ 29) - ((g + 1) * x - (g ^ 2 + g)) :=
  agreementAt_eval (2 ^ 29) g x

private theorem primitive_root {g : F} (hg : orderOf g = 2 ^ 30) :
    IsPrimitiveRoot g (2 ^ 30) := by
  rw [← hg]
  exact IsPrimitiveRoot.orderOf g

private theorem generator_ne_zero {g : F} (hg : orderOf g = 2 ^ 30) : g ≠ 0 := by
  intro h
  have hp := (primitive_root hg).pow_eq_one
  simp [h] at hp

private theorem generator_add_one_ne_zero {g : F} (hg : orderOf g = 2 ^ 30) :
    g + 1 ≠ 0 := by
  intro h
  have hneg : g = -1 := add_eq_zero_iff_eq_neg.mp h
  have hp := (primitive_root hg).pow_ne_one_of_pos_of_lt
    (l := 2) (by decide) (by norm_num)
  simp [hneg] at hp

/-- The head exponents satisfy the original even, high-degree, in-domain restrictions. -/
theorem head_exponents :
    Even (2 ^ 29) ∧ Even (2 ^ 29 + 2) ∧
      (2 ^ 29 : ℕ) < 2 ^ 29 + 2 ∧ (2 ^ 29 + 2 : ℕ) < 2 ^ 30 := by
  norm_num [even_iff_two_dvd]

/-- Neither the high coefficient nor the linear tail coefficient vanishes. -/
theorem coefficients_ne_zero {g : F} (hg : orderOf g = 2 ^ 30) :
    -(g ^ 2) ≠ 0 ∧ g + 1 ≠ 0 :=
  ⟨neg_ne_zero.mpr (pow_ne_zero _ (generator_ne_zero hg)), generator_add_one_ne_zero hg⟩

/-- The tail has degree one, strictly below the actual code dimension. -/
theorem tail_degree {g : F} (hg : orderOf g = 2 ^ 30) :
    (tail g).natDegree = 1 ∧ (tail g).natDegree < 2 ^ 29 := by
  have hd : (tail g).natDegree = 1 := by
    rw [tail, natDegree_sub_C, natDegree_C_mul_X _ (generator_add_one_ne_zero hg)]
  exact ⟨hd, by rw [hd]; norm_num⟩

-- Prove evaluation identities with a symbolic exponent before specializing. This avoids
-- kernel reduction of the half-billion-degree polynomial power.
private theorem roots_aux (b : ℕ) (g : F) :
    (agreementAt b g).IsRoot 1 ∧ (agreementAt b g).IsRoot g := by
  unfold agreementAt
  constructor
  · simp only [IsRoot.def, tail, eval_sub, eval_pow, eval_X, eval_mul, eval_C,
      one_pow, mul_one]
    ring
  · simp only [IsRoot.def, tail, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
    rw [pow_add]
    ring

/-- The two distinguished points are roots by polynomial identities alone. -/
theorem roots (g : F) : (agreement g).IsRoot 1 ∧ (agreement g).IsRoot g := by
  unfold agreement
  exact roots_aux (2 ^ 29) g

private theorem antipode_values_aux (b : ℕ) (hb : Even b) (g : F) :
    (agreementAt b g).eval (-1) = 2 * (g + 1) ∧
      (agreementAt b g).eval (-g) = 2 * g * (g + 1) := by
  unfold agreementAt
  have ha : Even (b + 2) := hb.add (by decide)
  constructor
  · simp only [tail, eval_sub, eval_pow, eval_X, eval_mul, eval_C,
      ha.neg_pow, hb.neg_pow, one_pow]
    ring
  · simp only [tail, eval_sub, eval_pow, eval_X, eval_mul, eval_C,
      ha.neg_pow, hb.neg_pow]
    rw [pow_add]
    ring

/-- Exact nonzero-candidate values at the antipodes, without enumerating the domain. -/
theorem antipode_values (g : F) :
    (agreement g).eval (-1) = 2 * (g + 1) ∧
      (agreement g).eval (-g) = 2 * g * (g + 1) := by
  unfold agreement
  exact antipode_values_aux (2 ^ 29) head_exponents.1 g

/-- Both antipodes fail to be roots in characteristic different from two. -/
theorem roots_and_antipodes {g : F} (hg : orderOf g = 2 ^ 30) (hchar : (2 : F) ≠ 0) :
    (agreement g).IsRoot 1 ∧ (agreement g).IsRoot g ∧
      ¬ (agreement g).IsRoot (-1) ∧ ¬ (agreement g).IsRoot (-g) := by
  refine ⟨(roots g).1, (roots g).2, ?_, ?_⟩
  · rw [IsRoot.def, (antipode_values g).1]
    exact mul_ne_zero hchar (generator_add_one_ne_zero hg)
  · rw [IsRoot.def, (antipode_values g).2]
    exact mul_ne_zero (mul_ne_zero hchar (generator_ne_zero hg))
      (generator_add_one_ne_zero hg)

/-- The roots and their antipodes all lie on the actual order-`2^30` domain. -/
theorem domain_membership {g : F} (hg : orderOf g = 2 ^ 30) :
    (1 : F) ^ (2 ^ 30) = 1 ∧ g ^ (2 ^ 30) = 1 ∧
      (-1 : F) ^ (2 ^ 30) = 1 ∧ (-g) ^ (2 ^ 30) = 1 := by
  have he : Even (2 ^ 30) := by norm_num [even_iff_two_dvd]
  simp only [he.neg_pow, (primitive_root hg).pow_eq_one, one_pow, and_self]

/-- Distinct roots have opposite half-order powers, distinguishing the two cosets. -/
theorem opposite_cosets {g : F} (hg : orderOf g = 2 ^ 30) :
    (1 : F) ≠ g ∧ (1 : F) ^ (2 ^ 29) = 1 ∧ g ^ (2 ^ 29) = -1 := by
  refine ⟨Ne.symm ((primitive_root hg).ne_one (by norm_num)), one_pow _, ?_⟩
  exact ArkLib.ProximityGap.Frontier.PrimitiveTwoPowRootHalfPowerEqNegOne
    (k := 29) (primitive_root hg)

/-- The isolated on-domain roots are not contained in any translate of the half subgroup.
The set `{c * u | u^(2^29) = 1}` is a multiplicative coset when `c ≠ 0`;
allowing `c = 0` only strengthens this impossibility statement. -/
theorem not_isolated_roots_in_one_coset {g : F}
    (hg : orderOf g = 2 ^ 30) (hchar : (2 : F) ≠ 0) :
    ¬ ∃ c : F, ∀ x : F, x ^ (2 ^ 30) = 1 →
      (agreement g).IsRoot x → ¬ (agreement g).IsRoot (-x) →
        ∃ u : F, u ^ (2 ^ 29) = 1 ∧ x = c * u := by
  rintro ⟨c, hc⟩
  obtain ⟨h1, hgroot, hn1, hng⟩ := roots_and_antipodes hg hchar
  obtain ⟨u, hu, hcu⟩ := hc 1 (one_pow _) h1 hn1
  obtain ⟨v, hv, hcv⟩ := hc g (primitive_root hg).pow_eq_one hgroot hng
  have hc1 : c ^ (2 ^ 29) = 1 := by
    have h := congrArg (fun x : F ↦ x ^ (2 ^ 29)) hcu
    simpa only [one_pow, mul_pow, hu, mul_one] using h.symm
  have hg1 : g ^ (2 ^ 29) = 1 := by
    rw [hcv, mul_pow, hc1, hv, one_mul]
  have hneg : (-1 : F) = 1 := (opposite_cosets hg).2.2.symm.trans hg1
  apply hchar
  linear_combination -hneg

section FirstField

open ArkLib.ProximityGap.PrizeShapePrimeP30

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- Unconditional root and antipode certificate in the first sponsor field. -/
theorem first_field_roots :
    (agreement g).IsRoot 1 ∧ (agreement g).IsRoot g ∧
      ¬ (agreement g).IsRoot (-1) ∧ ¬ (agreement g).IsRoot (-g) := by
  exact roots_and_antipodes orderOf_g (by decide)

/-- Unconditional failure of isolated-root coset confinement in the first sponsor field. -/
theorem first_field_not_confined :
    ¬ ∃ c : ZMod P, ∀ x : ZMod P, x ^ (2 ^ 30) = 1 →
      (agreement g).IsRoot x → ¬ (agreement g).IsRoot (-x) →
        ∃ u : ZMod P, u ^ (2 ^ 29) = 1 ∧ x = c * u := by
  exact not_isolated_roots_in_one_coset orderOf_g (by decide)

end FirstField

section SecondField

open ArkLib.ProximityGap.PrizeShapePrimeP30Second

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- Unconditional root and antipode certificate in the second sponsor field. -/
theorem second_field_roots :
    (agreement g).IsRoot 1 ∧ (agreement g).IsRoot g ∧
      ¬ (agreement g).IsRoot (-1) ∧ ¬ (agreement g).IsRoot (-g) := by
  exact roots_and_antipodes orderOf_g (by decide)

/-- Unconditional failure of isolated-root coset confinement in the second sponsor field. -/
theorem second_field_not_confined :
    ¬ ∃ c : ZMod P, ∀ x : ZMod P, x ^ (2 ^ 30) = 1 →
      (agreement g).IsRoot x → ¬ (agreement g).IsRoot (-x) →
        ∃ u : ZMod P, u ^ (2 ^ 29) = 1 ∧ x = c * u := by
  exact not_isolated_roots_in_one_coset orderOf_g (by decide)

end SecondField

#print axioms tail_degree
#print axioms roots_and_antipodes
#print axioms domain_membership
#print axioms opposite_cosets
#print axioms first_field_not_confined
#print axioms second_field_not_confined

end

end ProximityGap.Frontier.AntipodalMixedCosetCounterexample
