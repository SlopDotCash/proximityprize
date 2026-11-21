/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.Polynomial.Bivariate

/-! # The coordinate/value weight of a trivariate polynomial -/

open Polynomial Finset
namespace ArkLib.ProximityGap.Frontier.SecondPrimeCoordinateWeight

variable {K : Type} [Field K]
abbrev Surface (K : Type) [Field K] := Polynomial (Polynomial K[X])

/-- Swap the coordinate and scalar axes, then substitute X^d Y for the value variable Y. -/
noncomputable def twist (d : ℕ) (P : Surface K) : Surface K :=
  (P.map Bivariate.swap.toRingHom).comp (C (X ^ d) * X)

/-- Maximum coordinate exponent plus d times the value exponent. -/
noncomputable def weight (d : ℕ) (P : Surface K) : ℕ := Bivariate.degreeX (twist d P)

private theorem twist_coeff (P : Surface K) (d j : ℕ) :
    (twist d P).coeff j = Bivariate.swap (P.coeff j) * X ^ (d * j) := by
  rw [twist, comp_C_mul_X_coeff, coeff_map, ← pow_mul]
  rfl

private theorem twist_coeff_degree (P : Surface K) (d j : ℕ) (hj : P.coeff j ≠ 0) :
    ((twist d P).coeff j).natDegree = Bivariate.degreeX (P.coeff j) + j * d := by
  have hs : Bivariate.swap (P.coeff j) ≠ 0 := by
    simpa only [map_zero] using Bivariate.swap.injective.ne hj
  rw [twist_coeff, natDegree_mul hs (pow_ne_zero _ X_ne_zero),
    natDegree_X_pow, Nat.mul_comm d j]
  exact congrArg (· + j * d) (Bivariate.natDegreeY_swap (P.coeff j))

private theorem twist_nonzero (P : Surface K) (d : ℕ) (hP : P ≠ 0) : twist d P ≠ 0 := by
  intro h
  have hj : P.coeff P.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hs : Bivariate.swap (P.coeff P.natDegree) ≠ 0 := by
    simpa only [map_zero] using Bivariate.swap.injective.ne hj
  apply mul_ne_zero hs (pow_ne_zero (d * P.natDegree) X_ne_zero)
  rw [← twist_coeff, h, coeff_zero]

/-- Weight is additive under multiplication of nonzero surfaces, including at scalar weight zero. -/
theorem weight_mul (d : ℕ) (P Q : Surface K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    weight d (P * Q) = weight d P + weight d Q := by
  have hm : twist d (P * Q) = twist d P * twist d Q := by simp [twist, Polynomial.map_mul, mul_comp]
  unfold weight
  rw [hm, Bivariate.degreeX_mul _ _ (twist_nonzero P d hP) (twist_nonzero Q d hQ)]

/-- Every nonzero trivariate coefficient has coordinate/value weight at most the surface weight. -/
theorem coeff_weight_le (d : ℕ) (P : Surface K) {j i a : ℕ}
    (h : ((P.coeff j).coeff i).coeff a ≠ 0) : a + j * d ≤ weight d P := by
  have hj : P.coeff j ≠ 0 := fun hz => h (by simp [hz])
  have ha := le_natDegree_of_ne_zero h
  have hi := Bivariate.coeff_natDegree_le_degreeX (P.coeff j) i
  have ht := Bivariate.coeff_natDegree_le_degreeX (twist d P) j
  rw [twist_coeff_degree P d j hj] at ht
  exact (Nat.add_le_add_right (ha.trans hi) _).trans ht

/-- A support-wide weight bound is also a bound on the actual multiplicative weight. -/
theorem weight_le_of_coeff (d : ℕ) (P : Surface K) {W : ℕ}
    (h : ∀ j i a, ((P.coeff j).coeff i).coeff a ≠ 0 → a + j * d ≤ W) :
    weight d P ≤ W := by
  classical
  apply Finset.sup_le
  intro j hj
  have hj' : P.coeff j ≠ 0 := by
    intro hz
    apply (mem_support_iff.mp hj)
    simp [twist_coeff, hz]
  rw [twist_coeff_degree P d j hj']
  obtain ⟨i, hi, heq, -⟩ := Bivariate.exists_max_index_degreeX (P.coeff j) hj'
  rw [← heq]
  exact h _ _ _ (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi))

#print axioms weight_mul
#print axioms coeff_weight_le
#print axioms weight_le_of_coeff
end ArkLib.ProximityGap.Frontier.SecondPrimeCoordinateWeight
