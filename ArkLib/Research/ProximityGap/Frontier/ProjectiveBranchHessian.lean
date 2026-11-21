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


variable [IsDomain R]

private theorem frac_form (F : R[X][X]) (h : ℕ) (x B A : R) (ha : A ≠ 0)
    (hf : F.natDegree ≤ h) :
    let φ := algebraMap R (FractionRing R)
    let ev := ((evalRingHom ((φ A)⁻¹ * φ B)).comp (mapRingHom φ)).comp
      (mapRingHom (evalRingHom x))
    φ (form F h x B A) = (φ A)^h * ev F := by
  dsimp only
  let φ := algebraMap R (FractionRing R)
  have hφ := IsFractionRing.injective R (FractionRing R)
  have hA : φ A ≠ 0 := fun hh => ha (hφ (hh.trans (map_zero φ).symm))
  let u := Units.mk0 (φ A) hA
  unfold form
  rw [BinaryBranchResultant.map_binaryValue _ hφ]
  exact BinaryBranchResultant.binaryValue_unit_right _ _ (natDegree_map_le.trans
    (natDegree_map_le.trans hf)) u _

/-- The degree-seven homogeneous value of the ordinary affine Hessian is its
three-term binary Hessian, including the case of a nonunit denominator. -/
theorem cubic_hessian_form (F : R[X][X]) (hF : F.natDegree ≤ 3) (x B A : R) (ha : A ≠ 0) :
    form (ScalarHessianLocalOrder.hessian F) 7 x B A =
      form (BranchHessianIdeal.scalar (BranchHessianIdeal.scalar F)) 3 x B A *
        (form F.derivative 2 x B A)^2 -
      2 * form (BranchHessianIdeal.scalar F).derivative 2 x B A *
        form F.derivative 2 x B A * form (BranchHessianIdeal.scalar F) 3 x B A +
      form F.derivative.derivative 1 x B A * (form (BranchHessianIdeal.scalar F) 3 x B A)^2 := by
  let Z := BranchHessianIdeal.scalar F
  let ZZ := BranchHessianIdeal.scalar Z
  have hZ : Z.natDegree ≤ 3 := (coeff_le F).trans hF
  have hZZ : ZZ.natDegree ≤ 3 := (coeff_le Z).trans hZ
  have hY : F.derivative.natDegree ≤ 2 := (natDegree_derivative_le F).trans
    (Nat.sub_le_sub_right hF 1)
  have hZY : Z.derivative.natDegree ≤ 2 := (natDegree_derivative_le Z).trans
    (Nat.sub_le_sub_right hZ 1)
  have hYY : F.derivative.derivative.natDegree ≤ 1 := (natDegree_derivative_le _).trans
    (Nat.sub_le_sub_right hY 1)
  let H := ZZ*F.derivative^2 - 2*Z.derivative*F.derivative*Z + F.derivative.derivative*Z^2
  have hH : H.natDegree ≤ 7 := by
    apply natDegree_add_le_of_degree_le
    · apply (natDegree_sub_le _ _).trans
      apply max_le
      · exact natDegree_mul_le_of_le hZZ (natDegree_pow_le_of_le 2 hY)
      · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le
          (natDegree_mul_le_of_le (le_of_eq (natDegree_ofNat 2)) hZY) hY) hZ
    · exact natDegree_mul_le_of_le hYY (natDegree_pow_le_of_le 2 hZ)
  let φ := algebraMap R (FractionRing R)
  apply IsFractionRing.injective R (FractionRing R)
  change φ (form H 7 x B A) = _
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  rw [frac_form H _ _ _ _ ha hH, frac_form ZZ _ _ _ _ ha hZZ, frac_form _ _ _ _ _ ha hY,
    frac_form _ _ _ _ _ ha hZY, frac_form Z _ _ _ _ ha hZ, frac_form _ _ _ _ _ ha hYY]
  simp only [H, map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- On a projective root the raw Hessian times the fourth power of the
denominator lies in the square of every ideal containing the two polars. -/
theorem projective_hessian_mem_square (F : R[X][X]) (hF : F.natDegree ≤ 3)
    (x B A : R) (ha : A ≠ 0) (hroot : form F 3 x B A = 0) (I : Ideal R)
    (hU : form (BranchHessianIdeal.coordinate F) 3 x B A ∈ I)
    (hV : A * form F.derivative 2 x B A ∈ I) :
    A^4 * form (ScalarHessianLocalOrder.hessian F) 7 x B A ∈ I^2 := by
  have hz : A^2 * form (BranchHessianIdeal.scalar F) 3 x B A ∈ I := by
    rw [cubic_scalar F hF x B A hroot]
    exact I.add_mem (I.mul_mem_right _ (I.mul_mem_left _ hU)) (I.mul_mem_left _ hV)
  have hy : A^2 * form F.derivative 2 x B A ∈ I := by
    rw [pow_two, mul_assoc]
    exact I.mul_mem_left _ hV
  rw [cubic_hessian_form F hF x B A ha, pow_two]
  convert (I*I).add_mem ((I*I).sub_mem
    ((I*I).mul_mem_left (form (BranchHessianIdeal.scalar (BranchHessianIdeal.scalar F)) 3 x B A)
      (Ideal.mul_mem_mul hy hy))
    ((I*I).mul_mem_left (2 * form (BranchHessianIdeal.scalar F).derivative 2 x B A)
      (Ideal.mul_mem_mul hy hz)))
    ((I*I).mul_mem_left (form F.derivative.derivative 1 x B A) (Ideal.mul_mem_mul hz hz)) using 1 <;> ring

#print axioms cubic_hessian_form
#print axioms projective_hessian_mem_square

#print axioms cubic_scalar
end ArkLib.ProximityGap.Frontier.ProjectiveBranchHessian
