/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Polynomial.Wronskian

/-! # Descent of differential constants from low-degree equations

In characteristic `p`, if a constant `c` satisfies `P(X,c)=0`, the coordinate
has nonzero derivative, and the coordinate degree of `P` is strictly less than
`p`, repeated coordinate differentiation gives a nonzero polynomial over the
coefficient field annihilating `c`. The coefficient field can be imperfect.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.PositiveCharacteristicHeightDescent

/-- Below the characteristic, no positive monomial survives with zero derivative. -/
theorem natDegree_eq_zero_of_derivative_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} [CharP R p] (f : R[X]) (hdeg : f.natDegree < p) (hd : f.derivative = 0) :
    f.natDegree = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  by_cases h : f.natDegree < i+1
  · exact coeff_eq_zero_of_natDegree_lt h
  have hn : (↑(i+1) : R) ≠ 0 := by
    intro he
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega : i+1 < p)
      ((CharP.cast_eq_zero_iff R p (i+1)).mp he)
  have hc := congrArg (fun q : R[X] => q.coeff i) hd
  simp only [coeff_derivative, coeff_zero] at hc
  exact (mul_eq_zero.mp hc).resolve_right (by simpa using hn)

private theorem deriv_mul {L : Type*} [Field L] [Differential L] (a b : L) :
    (a*b)′ = a*b′ + b*a′ := by
  simpa only [smul_eq_mul] using Differential.deriv.leibniz a b

/-- A reduced rational function of strict height below the characteristic with
zero derivative belongs to its coefficient field. The derivation is specified on
the embedded polynomial ring, which also uniquely determines its quotient rule. -/
theorem ratFunc_eq_constant {k : Type*} [Field k] {p : ℕ} [CharP k p]
    [Differential (RatFunc k)]
    (hder : ∀ a : k[X], (algebraMap k[X] (RatFunc k) a)′ = algebraMap _ _ a.derivative)
    (r : RatFunc k) (hn : r.num.natDegree < p) (hd : r.denom.natDegree < p)
    (hr : r′ = 0) : ∃ c : k, r = RatFunc.C c := by
  let A := algebraMap k[X] (RatFunc k)
  have hnum : A r.num = r * A r.denom :=
    (div_eq_iff (RatFunc.algebraMap_ne_zero r.denom_ne_zero)).mp (RatFunc.num_div_denom r)
  have hdiff := congrArg (fun z : RatFunc k => z′) hnum
  change (A r.num)′ = (r * A r.denom)′ at hdiff
  rw [deriv_mul, hr, mul_zero, add_zero] at hdiff
  have hder' (q : k[X]) : (A q)′ = A q.derivative := hder q
  rw [hder', hder'] at hdiff
  have hw : wronskian r.num r.denom = 0 := by
    apply RatFunc.algebraMap_injective k
    change A (r.num * r.denom.derivative - r.num.derivative * r.denom) = A 0
    rw [map_zero, map_sub, map_mul, map_mul, hnum, hdiff]
    ring
  obtain ⟨ha,hb⟩ := (RatFunc.isCoprime_num_denom r).wronskian_eq_zero_iff.mp hw
  exact (RatFunc.eq_C_iff r).mpr ⟨natDegree_eq_zero_of_derivative_eq_zero _ hn ha,
    natDegree_eq_zero_of_derivative_eq_zero _ hd hb⟩

/-- The coefficients of the monic minimal polynomial of a differential constant
are differential constants, including in positive characteristic. -/
theorem minpoly_coeff_deriv_zero {k L : Type*} [Field k] [Field L]
    [Differential k] [Differential L] [Algebra k L] [DifferentialAlgebra k L]
    (c : L) (hi : IsIntegral k c) (hc : c′ = 0) (i : ℕ) :
    ((minpoly k c).coeff i)′ = 0 := by
  let m := minpoly k c
  have he : aeval c (Differential.mapCoeffs m) = 0 := by
    have h := Differential.deriv_aeval_eq c m
    rw [show aeval c m = 0 from minpoly.aeval k c, map_zero, hc, mul_zero, add_zero] at h
    exact h.symm
  have hm : Differential.mapCoeffs m = 0 := by
    by_contra hn
    have hle : (Differential.mapCoeffs m).natDegree ≤ m.natDegree := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      simp [coeff_eq_zero_of_natDegree_lt hn]
    have heq := hle.antisymm (natDegree_le_of_dvd (minpoly.dvd k c he) hn)
    apply (leadingCoeff_ne_zero.mpr hn)
    rw [← coeff_natDegree, heq, Differential.coeff_mapCoeffs, coeff_natDegree,
      (minpoly.monic hi).leadingCoeff, Differential.deriv.map_one_eq_zero]
  exact (congrArg (fun q : k[X] => q.coeff i) hm : _)

/-- For a bounded annihilator, a single nonconstant coordinate with nonzero
derivative cannot make a transcendental differential constant algebraic.
The outer indeterminate is the coordinate and the inner one is the constant. -/
theorem isAlgebraic_of_low_coordinate_degree {k L : Type*} [Field k] [Field L]
    [Algebra k L] [Differential L] {p : ℕ} [CharP k p]
    (hk : ∀ a : k, (algebraMap k L a)′ = 0) (x c : L) (hx : x′ ≠ 0) (hc : c′ = 0)
    (P : k[X][X]) (hne : P ≠ 0) (hdeg : P.natDegree < p)
    (hroot : P.eval₂ (aeval c).toRingHom x = 0) : IsAlgebraic k c := by
  let _ : Differential k := ⟨0⟩
  let _ : DifferentialAlgebra k L := ⟨fun a => by
    rw [hk]; exact (map_zero (algebraMap k L)).symm⟩
  have hconst (q : k[X]) : (aeval c q)′ = 0 := by
    have hm : Differential.mapCoeffs q = 0 := by ext j; rfl
    rw [Differential.deriv_aeval_eq, hm, map_zero, hc, mul_zero, add_zero]
  let _ : Differential k[X] := ⟨0⟩
  let _ : Algebra k[X] L := (aeval c).toRingHom.toAlgebra
  let _ : DifferentialAlgebra k[X] L := ⟨fun q => by
    change (aeval c q)′ = aeval c 0
    rw [hconst, map_zero]⟩
  have hstep (q : k[X][X]) (hq : aeval x q = 0) : aeval x q.derivative = 0 := by
    have hm : Differential.mapCoeffs q = 0 := by ext j; rfl
    have h := Differential.deriv_aeval_eq x q
    rw [hq, map_zero, hm, map_zero, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hx
  change aeval x P = 0 at hroot
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
      by_cases hz : P.natDegree = 0
      · refine ⟨P.coeff 0, ?_, ?_⟩
        · intro ha
          exact hne ((eq_C_of_natDegree_eq_zero hz).trans (by simp [ha]))
        · rw [eq_C_of_natDegree_eq_zero hz, aeval_C] at hroot
          exact hroot
      · have hlt := natDegree_derivative_lt hz
        apply ih P.derivative.natDegree (by omega) P.derivative
        · intro ha
          exact hz (natDegree_eq_zero_of_derivative_eq_zero _ hdeg ha)
        · omega
        · exact hstep P hroot
        · rfl

end ArkLib.ProximityGap.Frontier.PositiveCharacteristicHeightDescent

open ArkLib.ProximityGap.Frontier.PositiveCharacteristicHeightDescent in
#print axioms isAlgebraic_of_low_coordinate_degree
open ArkLib.ProximityGap.Frontier.PositiveCharacteristicHeightDescent in
#print axioms minpoly_coeff_deriv_zero
open ArkLib.ProximityGap.Frontier.PositiveCharacteristicHeightDescent in
#print axioms ratFunc_eq_constant
