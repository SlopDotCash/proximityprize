/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.BranchHessianIdeal
import ArkLib.Research.ProximityGap.Frontier.BinaryBranchResultant

/-! # The raw Hessian on a projective cubic branch

Euler's identity clears the scalar derivative with two powers of the
denominator. The resulting square-ideal estimate is integral at a pole.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Differential
namespace ArkLib.ProximityGap.Frontier.ProjectiveBranchHessian
open BinaryBranchResultant (binaryValue)

variable {R : Type*} [CommRing R] [Differential R]

/-- Evaluate the coordinate and the homogeneous value variables. -/
def form (F : R[X][X]) (h : ℕ) (x B A : R) : R :=
  binaryValue (F.map (evalRingHom x)) h B A

private theorem form_expand (F : R[X][X]) (h : ℕ) (x B A : R) (hF : F.natDegree ≤ h) :
    form F h x B A = ∑ j ∈ Finset.range (h+1), (F.coeff j).eval x * B^j * A^(h-j) := by
  unfold form binaryValue
  rw [Polynomial.sum_over_range' _ (fun _ => by simp) (h+1)
    (Nat.lt_succ_of_le (natDegree_map_le.trans hF))]
  simp only [coeff_map, coe_evalRingHom]

private theorem coeff_le {S : Type*} [CommRing S] [Differential S] (F : S[X]) :
    (Differential.mapCoeffs F).natDegree ≤ F.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp [Differential.coeff_mapCoeffs, coeff_eq_zero_of_natDegree_lt hn]

local instance : Differential R[X] := ⟨Differential.mapCoeffs⟩

private theorem coordinate_le (F : R[X][X]) :
    (BranchHessianIdeal.coordinate F).natDegree ≤ F.natDegree := by
  letI : Differential R[X] := ⟨(Polynomial.derivative' (R := R)).restrictScalars ℤ⟩
  exact coeff_le F

private theorem deriv_inner (p : R[X]) (x : R) :
    (p.eval x)′ = (Differential.mapCoeffs p).eval x + p.derivative.eval x*x′ := by
  simpa using Differential.deriv_aeval_eq x p

private theorem coeff_coordinate (F : R[X][X]) (j : ℕ) :
    (BranchHessianIdeal.coordinate F).coeff j = (F.coeff j).derivative := by
  letI : Differential R[X] := ⟨(Polynomial.derivative' (R := R)).restrictScalars ℤ⟩
  unfold BranchHessianIdeal.coordinate
  rw [Differential.coeff_mapCoeffs]
  rfl

/-- The scalar partial of the actual homogeneous cubic, after multiplication
by the square of the denominator, is an integral combination of its two polars. -/
theorem cubic_scalar (F : R[X][X]) (hF : F.natDegree ≤ 3) (x B A : R)
    (hroot : form F 3 x B A = 0) :
    A^2 * form (BranchHessianIdeal.scalar F) 3 x B A =
      -A^2 * form (BranchHessianIdeal.coordinate F) 3 x B A * x′ +
      (B * A′ - A * B′) * (A * form F.derivative 2 x B A) := by
  rw [form_expand _ _ _ _ _ hF] at hroot
  have hscalar : (BranchHessianIdeal.scalar F).natDegree ≤ 3 := (coeff_le F).trans hF
  rw [form_expand _ _ _ _ _ hscalar,
      form_expand _ _ _ _ _ ((coordinate_le F).trans hF),
      form_expand _ _ _ _ _ ((natDegree_derivative_le F).trans (Nat.sub_le_sub_right hF 1))]
  simp [Finset.sum_range_succ] at hroot
  have dh := congrArg (fun t : R => t′) hroot
  simp only [map_add, map_zero, Differential.deriv.leibniz, Differential.deriv.leibniz_pow,
    smul_eq_mul, nsmul_eq_mul, deriv_inner] at dh
  simp [Finset.sum_range_succ, BranchHessianIdeal.scalar, Differential.coeff_mapCoeffs,
    coeff_coordinate, coeff_derivative, Nat.cast_ofNat] at *
  linear_combination A^2 * dh - 3*A*A′ * hroot

#print axioms cubic_scalar
end ArkLib.ProximityGap.Frontier.ProjectiveBranchHessian
