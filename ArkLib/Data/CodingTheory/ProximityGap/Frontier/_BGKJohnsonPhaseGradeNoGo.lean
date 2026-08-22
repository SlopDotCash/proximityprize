/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Johnson grades of the seven-subset phase vector: lower Newton vanishing does not isolate grade 7

For phases `w_x`, put `v(S)=prod_(x in S) w_x` on seven-subsets.  The tempting association-scheme
hypothesis is that subtracting the Wick/repeated Newton strata removes Johnson grades `0,...,6`,
leaving only grade seven.  This file gives an exact counterexample.

Take the fourteen phases `1,zeta,...,zeta^13` for a primitive fourteenth root.  Every power sum
through degree seven vanishes.  Nevertheless, at the seven-subset of even exponents, the Johnson
replacement-adjacency sum is zero, whereas a pure grade-seven vector would have eigenvalue `-7`
and hence value `-7*v(S)`, which is nonzero.  Thus lower power-sum/Newton vanishing does not force
top Johnson grade.

The companion exact cyclotomic group-ring probe computes the complete grade masses.  With Johnson
eigenvalues `(49,35,23,13,5,-1,-5,-7)`, the masses are

`(0, 1/66, 7/6, 273/11, 637/3, 5005/6, 3003/2, 858)`.

Grades one through six carry exactly `2574`, or three quarters of the total norm `3432`; grade six
alone carries `3003/2 = 7/16 * 3432` and is the largest component.  The rational reconstruction
from the eight exact adjacency moments is kernel-checked below.  Johnson decomposition therefore
reorganizes, but does not remove, the load-bearing lower strata.  This example refutes a universal
phase/Newton identity; it is not a production multiplicative-subgroup instance, so an additional
finite-field arithmetic theorem could still force a different grade distribution.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKJohnsonPhaseGradeNoGo

/-! ## Exact primitive-fourteenth-root counterexample -/

/-- Power sum of the complete fourteen-phase family. -/
noncomputable def fullPhasePowerSum (zeta : Complex) (r : Nat) : Complex :=
  ∑ j ∈ Finset.range 14, (zeta ^ j) ^ r

/-- Every nonconstant power sum below degree fourteen vanishes. -/
theorem fullPhasePowerSum_eq_zero {zeta : Complex} (hzeta : IsPrimitiveRoot zeta 14)
    {r : Nat} (hr0 : 0 < r) (hr14 : r < 14) :
    fullPhasePowerSum zeta r = 0 := by
  have hne : zeta ^ r ≠ 1 := hzeta.pow_ne_one_of_pos_of_lt hr0.ne' hr14
  have hpow : (zeta ^ r) ^ 14 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hzeta.pow_eq_one, one_pow]
  have hgeom := geom_sum_mul (zeta ^ r) 14
  rw [hpow, sub_self] at hgeom
  have hsum : ∑ j ∈ Finset.range 14, (zeta ^ r) ^ j = 0 :=
    (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)
  unfold fullPhasePowerSum
  rw [show (∑ j ∈ Finset.range 14, (zeta ^ j) ^ r) =
      ∑ j ∈ Finset.range 14, (zeta ^ r) ^ j by
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
  exact hsum

theorem fullPhasePowerSums_one_through_seven {zeta : Complex}
    (hzeta : IsPrimitiveRoot zeta 14) :
    fullPhasePowerSum zeta 1 = 0 ∧
      fullPhasePowerSum zeta 2 = 0 ∧
      fullPhasePowerSum zeta 3 = 0 ∧
      fullPhasePowerSum zeta 4 = 0 ∧
      fullPhasePowerSum zeta 5 = 0 ∧
      fullPhasePowerSum zeta 6 = 0 ∧
      fullPhasePowerSum zeta 7 = 0 := by
  constructor
  · exact fullPhasePowerSum_eq_zero hzeta (by norm_num) (by norm_num)
  constructor
  · exact fullPhasePowerSum_eq_zero hzeta (by norm_num) (by norm_num)
  constructor
  · exact fullPhasePowerSum_eq_zero hzeta (by norm_num) (by norm_num)
  constructor
  · exact fullPhasePowerSum_eq_zero hzeta (by norm_num) (by norm_num)
  constructor
  · exact fullPhasePowerSum_eq_zero hzeta (by norm_num) (by norm_num)
  constructor <;> exact fullPhasePowerSum_eq_zero hzeta (by norm_num) (by norm_num)

noncomputable def evenWeight (zeta : Complex) (j : Fin 7) : Complex :=
  zeta ^ (2 * j.val)

noncomputable def oddWeight (zeta : Complex) (j : Fin 7) : Complex :=
  zeta ^ (2 * j.val + 1)

noncomputable def evenPhaseProduct (zeta : Complex) : Complex :=
  ∏ j : Fin 7, evenWeight zeta j

/-- Replacement form of the Johnson adjacency operator at the even-exponent seven-subset. -/
noncomputable def replacementAdjacencyAtEven (zeta : Complex) : Complex :=
  ∑ a : Fin 7, ∑ b : Fin 7,
    (∏ c ∈ (Finset.univ : Finset (Fin 7)).erase a, evenWeight zeta c) * oddWeight zeta b

theorem evenWeight_sum_zero {zeta : Complex} (hzeta : IsPrimitiveRoot zeta 14) :
    ∑ j : Fin 7, evenWeight zeta j = 0 := by
  have hzeta2 : IsPrimitiveRoot (zeta ^ 2) 7 :=
    hzeta.pow (by norm_num) (by norm_num)
  rw [show (∑ j : Fin 7, evenWeight zeta j) = ∑ j : Fin 7, (zeta ^ 2) ^ j.val by
    apply Finset.sum_congr rfl
    intro j _
    rw [evenWeight, pow_mul]]
  rw [Fin.sum_univ_eq_sum_range]
  exact hzeta2.geom_sum_eq_zero (by norm_num)

theorem oddWeight_sum_zero {zeta : Complex} (hzeta : IsPrimitiveRoot zeta 14) :
    ∑ j : Fin 7, oddWeight zeta j = 0 := by
  calc
    (∑ j : Fin 7, oddWeight zeta j) = ∑ j : Fin 7, (zeta ^ 2) ^ j.val * zeta := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [oddWeight, pow_add, pow_one, pow_mul]
    _ = (∑ j : Fin 7, (zeta ^ 2) ^ j.val) * zeta := by rw [Finset.sum_mul]
    _ = 0 := by
      have hzero : ∑ j : Fin 7, (zeta ^ 2) ^ j.val = 0 := by
        simpa [evenWeight, pow_mul] using evenWeight_sum_zero hzeta
      rw [hzero, zero_mul]

theorem replacementAdjacencyAtEven_eq_zero {zeta : Complex}
    (hzeta : IsPrimitiveRoot zeta 14) :
    replacementAdjacencyAtEven zeta = 0 := by
  unfold replacementAdjacencyAtEven
  calc
    (∑ a : Fin 7, ∑ b : Fin 7,
      (∏ c ∈ (Finset.univ : Finset (Fin 7)).erase a, evenWeight zeta c) * oddWeight zeta b) =
        ∑ a : Fin 7,
          (∏ c ∈ (Finset.univ : Finset (Fin 7)).erase a, evenWeight zeta c) *
            (∑ b : Fin 7, oddWeight zeta b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    _ = 0 := by rw [oddWeight_sum_zero hzeta]; simp

theorem evenPhaseProduct_ne_zero {zeta : Complex} (hzeta : IsPrimitiveRoot zeta 14) :
    evenPhaseProduct zeta ≠ 0 := by
  unfold evenPhaseProduct evenWeight
  apply (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
  exact pow_ne_zero _ (hzeta.ne_zero (by norm_num))

/-- **Concrete grade-seven refutation.**  Pure Johnson grade seven would satisfy the eigenrelation
`A v = -7 v`; the primitive-fourteenth-root phase vector fails it at the even subset. -/
theorem replacementAdjacencyAtEven_ne_gradeSeven {zeta : Complex}
    (hzeta : IsPrimitiveRoot zeta 14) :
    replacementAdjacencyAtEven zeta ≠ (-7 : Complex) * evenPhaseProduct zeta := by
  rw [replacementAdjacencyAtEven_eq_zero hzeta]
  exact Ne.symm (mul_ne_zero (by norm_num) (evenPhaseProduct_ne_zero hzeta))

/-! ## Exact rational grade-mass reconstruction -/

def johnson14Eigenvalue : Fin 8 -> Rat :=
  ![49, 35, 23, 13, 5, -1, -5, -7]

/-- Exact moments `<v,A^m v>`, computed in `Q[zeta_14]` by the companion probe. -/
def phaseAdjacencyMoment : Fin 8 -> Rat :=
  ![3432, -12936, 90552, -386904, 4190088, -930216, 448075992, 5697121416]

/-- Johnson idempotent masses obtained by exact Vandermonde inversion. -/
def phaseGradeMass : Fin 8 -> Rat :=
  ![0, 1 / 66, 7 / 6, 273 / 11, 637 / 3, 5005 / 6, 3003 / 2, 858]

/-- The eight masses reconstruct every adjacency moment exactly. -/
theorem phaseAdjacencyMoment_eq_spectral_sum (m : Fin 8) :
    phaseAdjacencyMoment m =
      ∑ i : Fin 8, johnson14Eigenvalue i ^ m.val * phaseGradeMass i := by
  fin_cases m <;>
    norm_num [phaseAdjacencyMoment, johnson14Eigenvalue, phaseGradeMass, Fin.sum_univ_succ]

theorem phaseGradeMass_total : ∑ i : Fin 8, phaseGradeMass i = 3432 := by
  norm_num [phaseGradeMass, Fin.sum_univ_succ]

theorem phaseGradeMass_zero : phaseGradeMass 0 = 0 := by
  norm_num [phaseGradeMass]

theorem phaseGradeMass_one_through_six_positive :
    0 < phaseGradeMass 1 ∧ 0 < phaseGradeMass 2 ∧ 0 < phaseGradeMass 3 ∧
      0 < phaseGradeMass 4 ∧ 0 < phaseGradeMass 5 ∧ 0 < phaseGradeMass 6 := by
  change (0 : Rat) < 1 / 66 ∧ 0 < 7 / 6 ∧ 0 < 273 / 11 ∧
    0 < 637 / 3 ∧ 0 < 5005 / 6 ∧ 0 < 3003 / 2
  norm_num

/-- Lower grades carry exactly three quarters of the norm; top grade carries one quarter. -/
theorem lowerGradeMass_three_times_top :
    phaseGradeMass 1 + phaseGradeMass 2 + phaseGradeMass 3 +
        phaseGradeMass 4 + phaseGradeMass 5 + phaseGradeMass 6 =
      3 * phaseGradeMass 7 := by
  change (1 / 66 : Rat) + 7 / 6 + 273 / 11 + 637 / 3 + 5005 / 6 + 3003 / 2 =
    3 * 858
  norm_num

/-- Grade six is load-bearing: it is the largest single grade and contains `7/16` of the norm. -/
theorem gradeSix_is_largest (i : Fin 8) : phaseGradeMass i ≤ phaseGradeMass 6 := by
  fin_cases i
  · change (0 : Rat) ≤ 3003 / 2
    norm_num
  · change (1 / 66 : Rat) ≤ 3003 / 2
    norm_num
  · change (7 / 6 : Rat) ≤ 3003 / 2
    norm_num
  · change (273 / 11 : Rat) ≤ 3003 / 2
    norm_num
  · change (637 / 3 : Rat) ≤ 3003 / 2
    norm_num
  · change (5005 / 6 : Rat) ≤ 3003 / 2
    norm_num
  · exact le_rfl
  · change (858 : Rat) ≤ 3003 / 2
    norm_num

theorem gradeSix_share : 16 * phaseGradeMass 6 = 7 * 3432 := by
  change (16 : Rat) * (3003 / 2) = 7 * 3432
  norm_num

#print axioms fullPhasePowerSum_eq_zero
#print axioms fullPhasePowerSums_one_through_seven
#print axioms evenWeight_sum_zero
#print axioms oddWeight_sum_zero
#print axioms replacementAdjacencyAtEven_eq_zero
#print axioms replacementAdjacencyAtEven_ne_gradeSeven
#print axioms phaseAdjacencyMoment_eq_spectral_sum
#print axioms phaseGradeMass_total
#print axioms lowerGradeMass_three_times_top
#print axioms gradeSix_is_largest

end ArkLib.ProximityGap.Frontier.BGKJohnsonPhaseGradeNoGo
