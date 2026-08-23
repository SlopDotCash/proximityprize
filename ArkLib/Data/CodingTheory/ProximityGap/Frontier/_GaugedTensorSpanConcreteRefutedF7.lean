/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GaugedLocalParityTensorModel
import Mathlib.Algebra.Field.ZMod

/-!
# Gauged tensor-span fullness is not automatic: an explicit F_7 counterexample

This exact small certificate has five distinct scalar labels, six distinct nonzero evaluation
nodes, degree bound two, and every label incident at least twice.  Nevertheless a nonzero gauged
degree-one polynomial family satisfies every local affine/parity constraint.  Therefore the
concrete `GaugedTensorSpanFull` proposition is false for this support topology.

This refutes universal maximal recoverability from coarse incidence/Hall-style data alone.  It is
not a Reed--Solomon MCA counterexample at the P1 parameters and does not refute a producer using
additional event geometry.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial

namespace ArkLib.ProximityGap.Frontier.GaugedTensorSpanConcreteRefutedF7

open SupportDividedDifferenceOperator
open SupportDividedDifferenceCoefficientFactorization
open GaugedLocalParityTensorModel

abbrev F7 := ZMod 7
abbrev Coord := Fin 6
abbrev Label := Fin 5

local instance localInstance_GaugedTensorSpanConcreteRefutedF7_1 : Fact (Nat.Prime 7) := ⟨by decide⟩

def domain : Coord → F7 := fun x => x.val + 1
def label : Label → F7 := fun j => j.val

def support : Coord → Finset Label
  | 0 => {0, 2, 3, 4}
  | 1 => {0, 3, 4}
  | 2 => {0, 1, 2}
  | 3 => {0, 3, 4}
  | 4 => {0, 1, 3, 4}
  | 5 => {0, 3, 4}

/-- Nonzero degree-one gauged kernel family: coefficient vector
`(q₂,q₃,q₄)=((4,1),(5,6),(2,1))`. -/
noncomputable def q : Label → F7[X]
  | 0 => 0
  | 1 => 0
  | 2 => C 4 + X
  | 3 => C 5 + C 6 * X
  | 4 => C 2 + X

def slope : Coord → F7
  | 0 => 6
  | 1 => 1
  | 2 => 0
  | 3 => 5
  | 4 => 0
  | 5 => 2

theorem domain_injective : Function.Injective domain := by
  decide

theorem label_injective : Function.Injective label := by
  decide

/-- Every label occurs on at least the degree bound's two coordinates. -/
theorem every_label_degree_ge_two (j : Label) :
    2 ≤ (Finset.univ.filter fun x : Coord => j ∈ support x).card := by
  fin_cases j <;> decide

/-- The three non-anchor labels whose polynomial coefficients remain after gauging. -/
def nonAnchors : Finset Label := {2, 3, 4}

/-- The same local codimension-two budget used by the P1 small-subset localization lane, defined
locally so this exact certificate remains independently fast-checkable. -/
def projectedBudget (U : Finset Label) : Nat :=
  ∑ x : Coord, min (support x ∩ U).card ((support x).card - 2)

/-- Every projected Hall inequality on the gauged label set is satisfied.  Thus the failure below
is genuinely a maximal-recoverability failure, not a dimension-budget obstruction. -/
theorem projectedHall_safe :
    ∀ U : Finset Label, U ⊆ nonAnchors →
      2 * U.card ≤ projectedBudget U := by
  decide

theorem q_degreeLT_two (j : Label) : q j ∈ Polynomial.degreeLT F7 2 := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn1' : 1 ≠ n := Ne.symm hn1
  fin_cases j <;> simp [q, Polynomial.coeff_C, Polynomial.coeff_X, hn0, hn1']

theorem q_supportedAgreement :
    SupportedAgreement domain support label q (fun _ => 0) slope := by
  intro x j hj
  fin_cases x <;> fin_cases j <;>
    simp [support] at hj <;>
    simp [q, domain, label, slope] <;> decide

theorem q_mem_kernel :
    q ∈ (supportDividedDifference domain support label).ker :=
  mem_ker_of_supportedAgreement domain support label q (fun _ => 0) slope q_supportedAgreement

theorem q_anchor_zero : q 0 = 0 ∧ q 1 = 0 := by
  simp [q]

theorem q_ne_zero : q ≠ 0 := by
  intro h
  have h2 := congrFun h (2 : Label)
  have hc := congrArg (fun p : F7[X] => p.coeff 0) h2
  have hfour : (4 : F7) ≠ 0 := by decide
  exact hfour (by simpa [q] using hc)

/-- **Concrete refutation.**  The gauged local-parity/Vandermonde tensor rows do not span the full
six-dimensional non-anchor coefficient dual. -/
theorem gaugedTensorSpanFull_refuted :
    ¬ GaugedTensorSpanFull domain label support 0 1 2 := by
  intro hspan
  have hzero := polynomial_family_eq_zero_of_gaugedTensorSpanFull
    domain label support hspan q q_degreeLT_two q_mem_kernel q_anchor_zero.1 q_anchor_zero.2
  exact q_ne_zero hzero

end ArkLib.ProximityGap.Frontier.GaugedTensorSpanConcreteRefutedF7

#print axioms ArkLib.ProximityGap.Frontier.GaugedTensorSpanConcreteRefutedF7.gaugedTensorSpanFull_refuted
#print axioms ArkLib.ProximityGap.Frontier.GaugedTensorSpanConcreteRefutedF7.projectedHall_safe
