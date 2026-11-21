/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarDividedLocator
import Mathlib.Algebra.Polynomial.Reverse

/-!
# The divided functional under the inverse coordinate

On the two affine charts of the projective coordinate line, reversing the
locator and the syndrome multiplies the divided functional by a signed power
of the universal root. The coefficient ring can have nilpotents.
-/

set_option autoImplicit false
namespace ProximityGap.ApolarDividedReversal

open Polynomial ApolarDividedLocator
variable {R : Type*} [CommRing R] [Nontrivial R]

omit [Nontrivial R] in
private theorem reflected_linear (x : Rˣ) :
    reflect 1 (X - C (x:R)) = (X - C ((↑x⁻¹):R)) * C (-(x:R)) := by
  rw [reflect_sub,reflect_one_X,reflect_C,pow_one,sub_mul,← C_mul]
  simp only [mul_neg,Units.inv_mul,map_neg,map_one]
  ring

private theorem divided_bound {r : ℕ} {f : R[X]} (x : R) (hf : f.natDegree ≤ r+1) :
    (divided f x).natDegree ≤ r := by
  rw [divided,natDegree_divByMonic _ (monic_X_sub_C _),natDegree_X_sub_C]
  omega

/-- Formula for the divided polynomial in the other affine chart. -/
theorem divided_reverse {r : ℕ} (x : Rˣ) (f : R[X]) (hf : f.natDegree ≤ r+1)
    (hx : f.IsRoot (x:R)) :
    divided (reflect (r+1) f) ((↑x⁻¹):R) = C (-(x:R))*reflect r (divided f x) := by
  have hprod : reflect (r+1) f =
      (X-C ((↑x⁻¹):R)) * (C (-(x:R))*reflect r (divided f x)) := by
    calc
      _ = reflect (1+r) ((X-C (x:R))*divided f x) := by rw [divided_identity f _ hx,Nat.add_comm]
      _ = _ := by
        rw [reflect_mul _ _ (by simp) (divided_bound _ hf),reflected_linear,mul_assoc]
  rw [divided,hprod,mul_divByMonic_cancel_left _ (monic_X_sub_C _)]

omit [Nontrivial R] in
private theorem reflect_higher (Q : R[X]) {r k : ℕ} (hq : Q.natDegree ≤ r) :
    reflect (r+k) (reflect r Q) = X^k*Q := by
  have hrev : (reflect r Q).natDegree ≤ r :=
    natDegree_reflect_le.trans (max_le le_rfl hq)
  have h := reflect_mul (reflect r Q) (1:R[X]) hrev (show (1:R[X]).natDegree ≤ k by simp)
  simpa [mul_comm] using h

/-- The reciprocal transition for the actual moment functional on the locator root algebra.
The degree of the locator is bounded by r+1 and the functional is taken through r+k. -/
theorem functional_reverse (L : R[X] →ₗ[R] R) {r k : ℕ} (hk : 0<k) (x : Rˣ)
    (f : R[X]) (hf : f.natDegree ≤ r+1) (hx : f.IsRoot (x:R))
    (ha : ApolarThrough L f (k-1)) :
    L (reflect (r+k) (divided (reflect (r+1) f) ((↑x⁻¹):R))) =
      -((x:R)^(k+1))*L (divided f (x:R)) := by
  rw [divided_reverse x f hf hx,reflect_C_mul, reflect_higher _ (divided_bound _ hf)]
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  have he := divided_evaluate L f (X^k) (x:R) hx ha
    (by rw [natDegree_X_pow]; omega)
  rw [mul_comm (X^k),he]
  simp [pow_succ,mul_assoc,mul_left_comm]

omit [Nontrivial R] in
/-- Reciprocal parameter chart: the locator has parameter degree l and the
functional is a pencil. Their divided value has parameter weight l+1. -/
theorem parameter_reverse (L₀ L₁ : R[X] →ₗ[R] R) (t : Rˣ) (l : ℕ)
    (f : R[X]) (z : R) (hz : f.IsRoot z) :
    (L₁ + ((↑t⁻¹):R) • L₀) (divided (C (((↑t⁻¹):R)^l)*f) z) =
      ((↑t⁻¹):R)^(l+1) * (L₀ + (t:R) • L₁) (divided f z) := by
  have eq : C (((↑t⁻¹):R)^l)*f =
      (X-C z)*(C (((↑t⁻¹):R)^l)*divided f z) := by rw [mul_left_comm,divided_identity f z hz]
  rw [divided,eq,mul_divByMonic_cancel_left _ (monic_X_sub_C _),← smul_eq_C_mul]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,map_smul,smul_eq_mul,pow_succ]
  linear_combination ((↑t⁻¹):R)^l * L₁ (divided f z) * (congrArg (fun c:R => c) t.inv_mul).symm

#print axioms divided_reverse
#print axioms functional_reverse
#print axioms parameter_reverse

end ProximityGap.ApolarDividedReversal
