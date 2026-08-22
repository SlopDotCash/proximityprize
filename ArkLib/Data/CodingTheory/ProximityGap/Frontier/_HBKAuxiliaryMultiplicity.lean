/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKConcreteConstraintMap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKNormalizedIncidenceUnion

/-!
# From the HBK constraint kernel to multiplicity

This file expands the special HBK auxiliary

`Phi(X) = sum lambda_(a,b,c) X^a X^(hb) (X-1)^(hc)`

and connects the concrete residual constraints `P_(m,u)=0` to vanishing of the iterated cleared
derivatives on the normalized incidence fibers.  This is the algebraic bridge in HBK Lemma 5.
Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.HBKAuxiliaryMultiplicity

open scoped BigOperators
open Polynomial
open HBKSpecialCoefficientKernel HBKClearedDerivativeRecurrence HBKConcreteConstraintMap
open HBKNormalizedIncidenceUnion

variable {F : Type*} [Field F] [DecidableEq F]

/-- The expanded univariate specialization of the HBK coefficient tensor. -/
noncomputable def expandedAuxiliary
    (h A B : ℕ) (coeffs : CoeffSpace F A B) : F[X] :=
  ∑ p : Fin A × Fin B × Fin B,
    C (coeffs p) * X ^ (p.1 : ℕ) * X ^ (h * (p.2.1 : ℕ)) *
      (X - 1) ^ (h * (p.2.2 : ℕ))

private theorem clearedDerivative_C_mul (c : F) (P : F[X]) :
    clearedDerivative (C c * P) = C c * clearedDerivative P := by
  simp only [clearedDerivative, Polynomial.derivative_mul, derivative_C, zero_mul, zero_add]
  ring

private theorem clearedDerivative_sum {I : Type*} [Fintype I] (f : I → F[X]) :
    clearedDerivative (∑ i, f i) = ∑ i, clearedDerivative (f i) := by
  simp only [clearedDerivative, derivative_sum]
  rw [Finset.mul_sum]

private theorem iterate_clearedDerivative_C_mul (c : F) (P : F[X]) (m : ℕ) :
    (clearedDerivative^[m]) (C c * P) = C c * (clearedDerivative^[m]) P := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        clearedDerivative_C_mul]

private theorem iterate_clearedDerivative_sum {I : Type*} [Fintype I]
    (f : I → F[X]) (m : ℕ) :
    (clearedDerivative^[m]) (∑ i, f i) = ∑ i, (clearedDerivative^[m]) (f i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, clearedDerivative_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Function.iterate_succ_apply']

/-- Iterating the cleared derivative on the expanded auxiliary gives exactly the residual family
used by the concrete constraint map. -/
theorem iterate_clearedDerivative_expandedAuxiliary
    (h A B : ℕ) (coeffs : CoeffSpace F A B) (m : ℕ) :
    (clearedDerivative^[m]) (expandedAuxiliary h A B coeffs) =
      ∑ p : Fin A × Fin B × Fin B,
        C (coeffs p) * residualPolynomial h p.1 p.2.1 p.2.2 m *
          X ^ (h * (p.2.1 : ℕ)) * (X - 1) ^ (h * (p.2.2 : ℕ)) := by
  rw [expandedAuxiliary, iterate_clearedDerivative_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [show
      C (coeffs p) * X ^ (p.1 : ℕ) * X ^ (h * (p.2.1 : ℕ)) *
          (X - 1) ^ (h * (p.2.2 : ℕ)) =
        C (coeffs p) *
          (X ^ (p.1 : ℕ) * X ^ (h * (p.2.1 : ℕ)) *
            (X - 1) ^ (h * (p.2.2 : ℕ))) by ring,
    iterate_clearedDerivative_C_mul,
    iterate_clearedDerivative_monomial]
  ring

/-- On a normalized fiber, evaluation of the cleared derivatives is evaluation of the concrete
constraint polynomial.  The two power identities are isolated explicitly so this lemma can also
be reused for other incidence-set realizations. -/
theorem eval_iterate_clearedDerivative_expandedAuxiliary_eq_constraintPolynomial
    (h A B : ℕ) (coeffs : CoeffSpace F A B) (m : ℕ) (u x : F)
    (hx : x ^ h = u⁻¹ ^ h) (hx1 : (x - 1) ^ h = u⁻¹ ^ h) :
    eval x ((clearedDerivative^[m]) (expandedAuxiliary h A B coeffs)) =
      eval x (constraintPolynomial h A B coeffs m u) := by
  rw [iterate_clearedDerivative_expandedAuxiliary, constraintPolynomial,
    eval_finset_sum, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  rw [pow_mul, hx, pow_mul, hx1]
  have hpow :
      (u⁻¹ ^ h) ^ (p.2.1 : ℕ) * (u⁻¹ ^ h) ^ (p.2.2 : ℕ) =
        u⁻¹ ^ (h * ((p.2.1 : ℕ) + (p.2.2 : ℕ))) := by
    rw [← pow_add, ← pow_mul]
  rw [show
      coeffs p * eval x (residualPolynomial h p.1 p.2.1 p.2.2 m) *
          (u⁻¹ ^ h) ^ (p.2.1 : ℕ) * (u⁻¹ ^ h) ^ (p.2.2 : ℕ) =
        coeffs p * eval x (residualPolynomial h p.1 p.2.1 p.2.2 m) *
          ((u⁻¹ ^ h) ^ (p.2.1 : ℕ) * (u⁻¹ ^ h) ^ (p.2.2 : ℕ)) by ring,
    hpow]
  ring

/-- Kernel membership forces every cleared derivative of order below `D` to vanish at every point
satisfying the normalized-fiber power identities. -/
theorem eval_iterate_clearedDerivative_eq_zero_of_mem_ker
    {h A B D : ℕ} {U : Finset F} {coeffs : CoeffSpace F A B}
    (hker : constraintMap h A B D U coeffs = 0)
    {m : ℕ} (hm : m < D) {u : F} (hu : u ∈ U) {x : F}
    (hx : x ^ h = u⁻¹ ^ h) (hx1 : (x - 1) ^ h = u⁻¹ ^ h) :
    eval x ((clearedDerivative^[m]) (expandedAuxiliary h A B coeffs)) = 0 := by
  rw [eval_iterate_clearedDerivative_expandedAuxiliary_eq_constraintPolynomial
    h A B coeffs m u x hx hx1,
    constraintPolynomial_eq_zero_of_mem_ker hker hm hu, eval_zero]

/-- Membership in a normalized HBK fiber gives both power identities, and also excludes the two
zeros of the clearing factor `X(X-1)`. -/
theorem normalizedFiber_power_identities
    {h : ℕ} (hh : 0 < h) {u x : F} (hu : u ≠ 0)
    (hx : x ∈ normalizedFiber (nthRootsFinset h (1 : F)) u) :
    x ^ h = u⁻¹ ^ h ∧ (x - 1) ^ h = u⁻¹ ^ h ∧ x ≠ 0 ∧ x ≠ 1 := by
  rw [normalizedFiber, Finset.mem_image] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hy' := Finset.mem_filter.mp hy
  have hyPow : y ^ h = (1 : F) := (mem_nthRootsFinset hh (1 : F)).mp hy'.1
  have hyuPow : (y - u) ^ h = (1 : F) :=
    (mem_nthRootsFinset hh (1 : F)).mp hy'.2
  have hy0 : y ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hy'.1
  have hyu0 : y - u ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hy'.2
  have hshift : u⁻¹ * y - 1 = u⁻¹ * (y - u) := by
    field_simp [hu]
  constructor
  · rw [← hxy, mul_pow, hyPow, mul_one]
  constructor
  · rw [← hxy, hshift, mul_pow, hyuPow, mul_one]
  constructor
  · rw [← hxy]
    exact mul_ne_zero (inv_ne_zero hu) hy0
  · rw [← hxy]
    intro hone
    exact hyu0 (by
      apply (mul_left_cancel₀ (inv_ne_zero hu))
      simpa [hshift] using sub_eq_zero.mpr hone)

/-- A concrete kernel vector makes every indexed cleared derivative vanish throughout the full
normalized incidence union. -/
theorem eval_iterate_clearedDerivative_eq_zero_on_incidenceUnion_of_mem_ker
    {h A B D : ℕ} (hh : 0 < h) {U : Finset F} {coeffs : CoeffSpace F A B}
    (hU0 : ∀ u ∈ U, u ≠ 0) (hker : constraintMap h A B D U coeffs = 0)
    {m : ℕ} (hm : m < D) {x : F}
    (hx : x ∈ incidenceUnion (nthRootsFinset h (1 : F)) U) :
    eval x ((clearedDerivative^[m]) (expandedAuxiliary h A B coeffs)) = 0 := by
  rw [incidenceUnion, Finset.mem_biUnion] at hx
  obtain ⟨u, hu, hxu⟩ := hx
  have hpows := normalizedFiber_power_identities hh (hU0 u hu) hxu
  exact eval_iterate_clearedDerivative_eq_zero_of_mem_ker hker hm hu hpows.1 hpows.2.1

private theorem eval_iterate_derivative_clearedDerivative_eq_zero
    (P : F[X]) (x : F) (n : ℕ)
    (hvanish : ∀ k ≤ n, eval x ((derivative^[k + 1]) P) = 0) :
    eval x ((derivative^[n]) (clearedDerivative P)) = 0 := by
  rw [clearedDerivative, iterate_derivative_mul, eval_finset_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  simp only [eval_smul, eval_mul]
  have hkder : eval x ((derivative^[k]) P.derivative) = 0 := by
    rw [← Function.iterate_succ_apply]
    exact hvanish k (by omega)
  rw [hkder, mul_zero, smul_zero]

private theorem eval_iterate_derivative_clearedDerivative_top
    (P : F[X]) (x : F) (n : ℕ)
    (hvanish : ∀ k < n, eval x ((derivative^[k + 1]) P) = 0) :
    eval x ((derivative^[n]) (clearedDerivative P)) =
      (x * (x - 1)) * eval x ((derivative^[n + 1]) P) := by
  rw [clearedDerivative, iterate_derivative_mul, eval_finset_sum]
  rw [Finset.sum_eq_single n]
  · simp only [Nat.choose_self, one_smul, Nat.sub_self, Function.iterate_zero_apply,
      eval_mul, eval_X, eval_sub, eval_one]
    rw [← Function.iterate_succ_apply]
  · intro k hk hkn
    rw [Finset.mem_range] at hk
    simp only [eval_smul, eval_mul]
    have hklt : k < n := by omega
    have hkder : eval x ((derivative^[k]) P.derivative) = 0 := by
      rw [← Function.iterate_succ_apply]
      exact hvanish k hklt
    rw [hkder, mul_zero, smul_zero]
  · simp

/-- At a point where all lower ordinary derivatives vanish, the `m`-th cleared derivative has
the same leading jet as the ordinary derivative, multiplied by `(x(x-1))^m`. -/
theorem eval_iterate_clearedDerivative_eq_leading_jet
    (P : F[X]) (x : F) (m : ℕ)
    (hvanish : ∀ j < m, eval x ((derivative^[j]) P) = 0) :
    eval x ((clearedDerivative^[m]) P) =
      (x * (x - 1)) ^ m * eval x ((derivative^[m]) P) := by
  induction m generalizing P with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      have hQvanish : ∀ j < m,
          eval x ((derivative^[j]) (clearedDerivative P)) = 0 := by
        intro j hj
        apply eval_iterate_derivative_clearedDerivative_eq_zero
        intro k hk
        exact hvanish (k + 1) (by omega)
      rw [ih (clearedDerivative P) hQvanish,
        eval_iterate_derivative_clearedDerivative_top P x m]
      · rw [pow_succ]
        ring
      · intro k hk
        exact hvanish (k + 1) (by omega)

/-- Vanishing of the first `D` cleared derivatives implies root multiplicity at least `D`, provided
the relevant factorial survives in the field and the clearing factor is nonzero at the point. -/
theorem le_rootMultiplicity_of_clearedDerivative_vanishing
    {P : F[X]} {x : F} {D : ℕ} (hP : P ≠ 0) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hfac : IsUnit (((D - 1).factorial : ℕ) : F))
    (hvanish : ∀ m < D, eval x ((clearedDerivative^[m]) P) = 0) :
    D ≤ P.rootMultiplicity x := by
  by_contra hD
  have hrD : P.rootMultiplicity x < D := Nat.lt_of_not_ge hD
  have hroot : P.IsRoot x := by
    rw [IsRoot]
    simpa using hvanish 0 (by omega)
  have hrpos : 0 < P.rootMultiplicity x := (rootMultiplicity_pos hP).mpr hroot
  have hlower : ∀ j < P.rootMultiplicity x,
      eval x ((derivative^[j]) P) = 0 := by
    intro j hj
    exact isRoot_iterate_derivative_of_lt_rootMultiplicity hj
  have hlead := eval_iterate_clearedDerivative_eq_leading_jet
    P x (P.rootMultiplicity x) hlower
  rw [hvanish (P.rootMultiplicity x) hrD] at hlead
  have hclearing : x * (x - 1) ≠ 0 := mul_ne_zero hx0 (sub_ne_zero.mpr hx1)
  have hderiv : eval x ((derivative^[P.rootMultiplicity x]) P) = 0 :=
    (mul_eq_zero.mp hlead.symm).resolve_left (pow_ne_zero _ hclearing)
  have heval := eval_iterate_derivative_rootMultiplicity (p := P) (t := x)
  rw [hderiv] at heval
  simp only [nsmul_eq_mul] at heval
  have hrle : P.rootMultiplicity x ≤ D - 1 := by omega
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hrle
  have hfacdvd : (((P.rootMultiplicity x).factorial : ℕ) : F) ∣
      (((D - 1).factorial : ℕ) : F) := by
    refine ⟨(c : F), ?_⟩
    rw [← Nat.cast_mul, ← hc]
  have hfacr : IsUnit (((P.rootMultiplicity x).factorial : ℕ) : F) :=
    isUnit_of_dvd_unit hfacdvd hfac
  have hquot : eval x (P /ₘ (X - C x) ^ P.rootMultiplicity x) ≠ 0 :=
    eval_divByMonic_pow_rootMultiplicity_ne_zero x hP
  exact hquot ((mul_eq_zero.mp heval.symm).resolve_left hfacr.ne_zero)

/-- The concrete coefficient kernel therefore gives multiplicity `D` on the entire normalized
incidence union.  The factorial-unit hypothesis is the precise characteristic condition needed
when ordinary rather than Hasse derivatives are used. -/
theorem le_rootMultiplicity_on_incidenceUnion_of_mem_ker
    {h A B D : ℕ} (hh : 0 < h) {U : Finset F} {coeffs : CoeffSpace F A B}
    (hU0 : ∀ u ∈ U, u ≠ 0) (haux : expandedAuxiliary h A B coeffs ≠ 0)
    (hfac : IsUnit (((D - 1).factorial : ℕ) : F))
    (hker : constraintMap h A B D U coeffs = 0) {x : F}
    (hx : x ∈ incidenceUnion (nthRootsFinset h (1 : F)) U) :
    D ≤ (expandedAuxiliary h A B coeffs).rootMultiplicity x := by
  rw [incidenceUnion, Finset.mem_biUnion] at hx
  obtain ⟨u, hu, hxu⟩ := hx
  have hpows := normalizedFiber_power_identities hh (hU0 u hu) hxu
  apply le_rootMultiplicity_of_clearedDerivative_vanishing
    haux hpows.2.2.1 hpows.2.2.2 hfac
  intro m hm
  exact eval_iterate_clearedDerivative_eq_zero_of_mem_ker
    hker hm hu hpows.1 hpows.2.1

end ArkLib.ProximityGap.Frontier.HBKAuxiliaryMultiplicity

#print axioms
  ArkLib.ProximityGap.Frontier.HBKAuxiliaryMultiplicity.iterate_clearedDerivative_expandedAuxiliary
#print axioms
  ArkLib.ProximityGap.Frontier.HBKAuxiliaryMultiplicity.eval_iterate_clearedDerivative_expandedAuxiliary_eq_constraintPolynomial
#print axioms
  ArkLib.ProximityGap.Frontier.HBKAuxiliaryMultiplicity.eval_iterate_clearedDerivative_eq_zero_of_mem_ker
#print axioms
  ArkLib.ProximityGap.Frontier.HBKAuxiliaryMultiplicity.normalizedFiber_power_identities
#print axioms
  ArkLib.ProximityGap.Frontier.HBKAuxiliaryMultiplicity.eval_iterate_clearedDerivative_eq_zero_on_incidenceUnion_of_mem_ker
#print axioms
  ArkLib.ProximityGap.Frontier.HBKAuxiliaryMultiplicity.eval_iterate_clearedDerivative_eq_leading_jet
#print axioms
  ArkLib.ProximityGap.Frontier.HBKAuxiliaryMultiplicity.le_rootMultiplicity_of_clearedDerivative_vanishing
#print axioms
  ArkLib.ProximityGap.Frontier.HBKAuxiliaryMultiplicity.le_rootMultiplicity_on_incidenceUnion_of_mem_ker
