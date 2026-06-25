/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Polynomial prize primes versus exponential height gates

Many #464 off-BGK or char-`p` transfer attempts have the same final shape:

* a fixed cyclotomic integer/resultant has a height or norm ceiling `B^d`, where
  `d = φ(2^μ) = 2^(μ-1) = n/2`;
* a prime `p` is certified good only when `B^d < p`;
* the prize regime only promises `p ≳ n^4`.

This file records the elementary quantitative obstruction.  If `n^β ≤ B^d`, then the prize lower
bound `p ≥ n^β` does not force the height gate `B^d < p`: the boundary prime `p = n^β` is a direct
counter-witness.  In the dyadic prize regime this obstruction appears even for the minimal
nontrivial base `B = 2`: for `n = 2^μ`, `μ ≥ 6`,

`n^4 ≤ 2^(n/2)`.

Thus any height/resultant route that only proves a generic `B^(n/2)` ceiling cannot certify all
prize-scale primes.  It needs extra arithmetic smoothness/localization of the actual resultant
prime divisors, not just an archimedean height bound.
-/

namespace ArkLib.ProximityGap.Frontier.PolynomialPrimeExponentialHeightGate

/-- A height gate certifies a prime `p` good when the height ceiling `B^d` is strictly below `p`. -/
def HeightGateFires (p B d : ℕ) : Prop := B ^ d < p

/-- Prize-scale lower bounds do not force a height gate when the height ceiling already exceeds the
prize scale.  The boundary value `p = n^β` satisfies the prize lower bound but not `B^d < p`. -/
theorem prizeScale_not_force_heightGate
    {n β B d : ℕ} (hscale : n ^ β ≤ B ^ d) :
    ∃ p : ℕ, n ^ β ≤ p ∧ ¬ HeightGateFires p B d :=
  ⟨n ^ β, le_rfl, by
    unfold HeightGateFires
    exact not_lt.mpr hscale⟩

/-- Contrapositive packaging: if the height gate fires already at the boundary prime `p = n^β`,
then the height ceiling must be strictly sub-prize-scale. -/
theorem boundary_heightGate_forces_subprize_height
    {n β B d : ℕ} (hgate : HeightGateFires (n ^ β) B d) :
    B ^ d < n ^ β := hgate

/-! ## Dyadic arithmetic: `n^4` is below even the base-2 exponential ceiling -/

/-- For `μ ≥ 6`, the dyadic degree exponent dominates the quartic exponent:
`4μ ≤ 2^(μ-1)`. -/
theorem four_mul_le_two_pow_pred : ∀ μ : ℕ, 6 ≤ μ -> 4 * μ ≤ 2 ^ (μ - 1)
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, h => by omega
  | 4, h => by omega
  | 5, h => by omega
  | 6, _ => by norm_num
  | μ + 7, _ => by
      have ih : 4 * (μ + 6) ≤ 2 ^ ((μ + 6) - 1) :=
        four_mul_le_two_pow_pred (μ + 6) (by omega)
      have hpow : 2 ^ ((μ + 7) - 1) = 2 * 2 ^ ((μ + 6) - 1) := by
        have h1 : (μ + 7) - 1 = ((μ + 6) - 1) + 1 := by omega
        rw [h1, pow_succ]
        ring
      rw [hpow]
      nlinarith

/-- For `n = 2^μ`, `μ ≥ 6`, the quartic prize scale is already below `2^(n/2)`. -/
theorem dyadic_quartic_le_base_two_height
    {μ : ℕ} (hμ : 6 ≤ μ) :
    ((2 : ℕ) ^ μ) ^ 4 ≤ 2 ^ (2 ^ (μ - 1)) := by
  have hexp : μ * 4 ≤ 2 ^ (μ - 1) := by
    have h := four_mul_le_two_pow_pred μ hμ
    omega
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hexp

/-- The dyadic quartic prize scale is below every exponential height ceiling `B^(n/2)` with
nontrivial base `B ≥ 2`, once `μ ≥ 6`. -/
theorem dyadic_quartic_le_exponential_height
    {μ B : ℕ} (hμ : 6 ≤ μ) (hB : 2 ≤ B) :
    ((2 : ℕ) ^ μ) ^ 4 ≤ B ^ (2 ^ (μ - 1)) := by
  exact le_trans (dyadic_quartic_le_base_two_height hμ) (Nat.pow_le_pow_left hB _)

/-- Therefore the prize lower bound `p ≥ n^4` does not force a generic height gate
`B^(n/2) < p` in the dyadic regime. -/
theorem dyadic_prizeScale_not_force_heightGate
    {μ B : ℕ} (hμ : 6 ≤ μ) (hB : 2 ≤ B) :
    ∃ p : ℕ,
      ((2 : ℕ) ^ μ) ^ 4 ≤ p ∧
        ¬ HeightGateFires p B (2 ^ (μ - 1)) :=
  prizeScale_not_force_heightGate
    (n := (2 : ℕ) ^ μ) (β := 4) (B := B) (d := 2 ^ (μ - 1))
    (dyadic_quartic_le_exponential_height hμ hB)

/-- Concrete first failure point: at `n = 64`, the quartic prize scale is `2^24`, while the
base-2 cyclotomic-degree height ceiling is `2^32`. -/
theorem n64_quartic_below_base_two_height :
    ((2 : ℕ) ^ 6) ^ 4 < 2 ^ (2 ^ (6 - 1)) := by
  norm_num

/-- At `n = 64`, the boundary prime scale `p = n^4` satisfies the prize lower bound but not even the
minimal base-2 height gate. -/
theorem n64_prizeScale_not_force_base_two_heightGate :
    ∃ p : ℕ,
      ((2 : ℕ) ^ 6) ^ 4 ≤ p ∧
        ¬ HeightGateFires p 2 (2 ^ (6 - 1)) :=
  dyadic_prizeScale_not_force_heightGate (μ := 6) (B := 2) (by norm_num) (by norm_num)

end ArkLib.ProximityGap.Frontier.PolynomialPrimeExponentialHeightGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.PolynomialPrimeExponentialHeightGate.prizeScale_not_force_heightGate
#print axioms ArkLib.ProximityGap.Frontier.PolynomialPrimeExponentialHeightGate.boundary_heightGate_forces_subprize_height
#print axioms ArkLib.ProximityGap.Frontier.PolynomialPrimeExponentialHeightGate.four_mul_le_two_pow_pred
#print axioms ArkLib.ProximityGap.Frontier.PolynomialPrimeExponentialHeightGate.dyadic_quartic_le_base_two_height
#print axioms ArkLib.ProximityGap.Frontier.PolynomialPrimeExponentialHeightGate.dyadic_quartic_le_exponential_height
#print axioms ArkLib.ProximityGap.Frontier.PolynomialPrimeExponentialHeightGate.dyadic_prizeScale_not_force_heightGate
#print axioms ArkLib.ProximityGap.Frontier.PolynomialPrimeExponentialHeightGate.n64_quartic_below_base_two_height
#print axioms ArkLib.ProximityGap.Frontier.PolynomialPrimeExponentialHeightGate.n64_prizeScale_not_force_base_two_heightGate
