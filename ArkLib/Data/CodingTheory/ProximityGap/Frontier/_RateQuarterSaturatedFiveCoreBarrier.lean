/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Connections.GCXK25SecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterPrimitiveFactorRecursion

/-!
# Rate-quarter saturated endpoint: integral five-core barrier

The quadratic Plotkin estimate rules out six saturated source cores.  At the
P1 endpoint, the integer-valued coordinate multiplicities give a sharper
fact: five cores are already impossible.

For five subsets, let `s_x` be the number containing coordinate `x`.  Since
`s_x \le 5`, the pointwise integer inequality

```text
5 s_x \le s_x^2 + 6
```

is exact at multiplicities two and three.  After double counting, it gives

```text
4 * sum_i |S_i| \le 6n + 20 lambda
```

when every distinct pair intersects in at most `lambda`.  Substituting
`n=16m`, `lambda=4m-2`, and the saturated core identity
`6z=53m-8` is contradictory for `m>10`.

This is strictly stronger than the real/quadratic Plotkin barrier and reduces
the global saturated-source frontier from five lines to at most four.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.RateQuarterSaturatedFiveCoreBarrier

open GCXK25SecondMoment
open HalfPredecessorLineCoreGeometry
open HalfPredecessorRateQuarterDeterminantCollapse
open HalfPredecessorRateQuarterPrimitiveDirection
open HalfPredecessorRateQuarterPrimitiveFactorRecursion

attribute [local instance] Classical.propDecidable

variable {U : Type} [Fintype U] [DecidableEq U]

/-- The integer improvement over Cauchy--Schwarz for a multiplicity bounded
by five. -/
theorem five_mul_le_sq_add_six {s : Nat} (hs : s ≤ 5) :
    5 * s ≤ s ^ 2 + 6 := by
  interval_cases s <;> norm_num

/-- **Integral five-set Johnson inequality.**  Five sets of size at least
`z`, with pair intersections at most `lambda`, satisfy
`20z ≤ 6|U|+20lambda`. -/
theorem fiveCore_integral_johnson
    (S : Fin 5 → Finset U) {z lambda : Nat}
    (hsize : ∀ i, z ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ lambda) :
    20 * z ≤ 6 * Fintype.card U + 20 * lambda := by
  classical
  let T : Finset (Fin 5) := Finset.univ
  let mass : Nat := ∑ i : Fin 5, (S i).card
  let second : Nat := ∑ i : Fin 5, ∑ j : Fin 5, (S i ∩ S j).card
  have hmassLower : 5 * z ≤ mass := by
    change 5 * z ≤ ∑ i : Fin 5, (S i).card
    rw [show 5 * z = ∑ _i : Fin 5, z by simp]
    exact Finset.sum_le_sum (fun i _ => hsize i)
  have hmultBound : ∀ x : U, mult T S x ≤ 5 := by
    intro x
    calc
      mult T S x = (T.filter fun i => x ∈ S i).card := rfl
      _ ≤ T.card := Finset.card_filter_le _ _
      _ = 5 := by simp [T]
  have hpoint : ∀ x : U,
      5 * mult T S x ≤ (mult T S x) ^ 2 + 6 := by
    intro x
    exact five_mul_le_sq_add_six (hmultBound x)
  have hfirstMoment : mass = ∑ x : U, mult T S x := by
    simpa [mass, T] using (sum_card_eq_sum_mult T S)
  have hsecondMoment : second = ∑ x : U, (mult T S x) ^ 2 := by
    simpa [second, T] using (sum_sum_card_inter_eq_sum_mult_sq T S)
  have hintegral : 5 * mass ≤ second + 6 * Fintype.card U := by
    rw [hfirstMoment, Finset.mul_sum]
    calc
      ∑ x : U, 5 * mult T S x
          ≤ ∑ x : U, ((mult T S x) ^ 2 + 6) :=
            Finset.sum_le_sum (fun x _ => hpoint x)
      _ = (∑ x : U, (mult T S x) ^ 2) + 6 * Fintype.card U := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_const, Finset.card_univ, Nat.mul_comm]
      _ = second + 6 * Fintype.card U := by rw [hsecondMoment]
  have hoffdiag :
      ∑ i ∈ T, ∑ j ∈ T.erase i, (S i ∩ S j).card ≤ 20 * lambda := by
    have h := offdiag_le T S (B := lambda) (by
      intro i hi j hj hij
      exact hpair i j hij)
    simpa [T] using h
  have hsplit := sum_sum_card_inter_eq_diag_add_offdiag T S
  have hsecondUpper : second ≤ mass + 20 * lambda := by
    have hdiag : ∑ i ∈ T, (S i).card = mass := by simp [T, mass]
    have hsecond :
        ∑ i ∈ T, ∑ j ∈ T, (S i ∩ S j).card = second := by
      simp [T, second]
    rw [hsecond, hdiag] at hsplit
    rw [hsplit]
    exact Nat.add_le_add_left hoffdiag mass
  have hfourMass : 4 * mass ≤ 6 * Fintype.card U + 20 * lambda := by
    have hcombined : 5 * mass ≤ mass + 20 * lambda + 6 * Fintype.card U :=
      hintegral.trans (Nat.add_le_add_right hsecondUpper (6 * Fintype.card U))
    omega
  have htwenty : 20 * z ≤ 4 * mass := by
    nlinarith
  exact htwenty.trans hfourMass

/-- Five saturated-size cores in a `16m`-point universe force a pair
intersection above the degree-`4m-2` cap. -/
theorem exists_pair_inter_card_ge_four_mul_sub_one_of_five
    {m z : Nat} (hm : 10 < m) (hz : 6 * z = 53 * m - 8)
    (hU : Fintype.card U = 16 * m)
    (S : Fin 5 → Finset U)
    (hsize : ∀ i, z ≤ (S i).card) :
    ∃ i j : Fin 5, i ≠ j ∧ 4 * m - 1 ≤ (S i ∩ S j).card := by
  by_contra hnot
  push Not at hnot
  have hpair : ∀ i j : Fin 5, i ≠ j →
      (S i ∩ S j).card ≤ 4 * m - 2 := by
    intro i j hij
    have := hnot i j hij
    omega
  have hJ := fiveCore_integral_johnson S hsize hpair
  rw [hU] at hJ
  have hm8 : 8 ≤ 53 * m := by omega
  have hz' : 6 * z + 8 = 53 * m := by omega
  omega

section PrimitiveCluster

open Polynomial

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A primitive collapsed cluster contains at most four distinct factors at
the saturated endpoint. -/
theorem not_five_saturated_cores_in_primitive_cluster
    (dom : I ↪ F) (u0 u1 : I → F)
    {m z : Nat} (hm : 10 < m) (hz : 6 * z = 53 * m - 8)
    (hI : Fintype.card I = 16 * m)
    (line0 line1 : PolynomialLine F) (hne : line0 ≠ line1)
    (source : Fin 5 → PolynomialLine F)
    (factor : Fin 5 → F[X]) (hfactor : Function.Injective factor)
    (hfactorDeg : ∀ i, (factor i).natDegree < 4 * m - 1)
    (hA : ∀ i, (source i).1 - line0.1 =
      primitiveIntercept line0 line1 * factor i)
    (hR : ∀ i, (source i).2 - line0.2 =
      primitiveSlope line0 line1 * factor i)
    (hcore : ∀ i, z ≤
      (jointCore dom u0 u1 (source i).1 (source i).2).card) :
    False := by
  let S : Fin 5 → Finset I := fun i =>
    jointCore dom u0 u1 (source i).1 (source i).2
  obtain ⟨i, j, hij, hlarge⟩ :=
    exists_pair_inter_card_ge_four_mul_sub_one_of_five hm hz hI S hcore
  have hcap := core_intersection_card_le_factor_dimension_pred
    dom u0 u1 line0 line1 (source i) (source j)
      (factor i) (factor j) (ell := 4 * m - 1)
      hne (hfactor.ne hij) (hfactorDeg i) (hfactorDeg j)
      (hA i) (hR i) (hA j) (hR j)
  change (S i ∩ S j).card ≤ (4 * m - 1) - 1 at hcap
  have hpred : (4 * m - 1) - 1 = 4 * m - 2 := by omega
  rw [hpred] at hcap
  omega

end PrimitiveCluster

end ArkLib.ProximityGap.Frontier.RateQuarterSaturatedFiveCoreBarrier

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateQuarterSaturatedFiveCoreBarrier
#print axioms fiveCore_integral_johnson
#print axioms exists_pair_inter_card_ge_four_mul_sub_one_of_five
#print axioms not_five_saturated_cores_in_primitive_cluster
