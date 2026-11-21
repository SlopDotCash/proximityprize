/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarCoordinateEquations
import ArkLib.Research.ProximityGap.Frontier.ApolarMomentCoordinates
import ArkLib.Data.CodingTheory.AGL24NonzeroMinor
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Generic coprimality from integral minimality

An injective rectangular moment matrix retains a full square minor after
embedding the coefficient domain in any field. In particular the divided
polynomial is nonzero at every geometric root of a minimal locator.
-/

set_option autoImplicit false
open Finset Polynomial Matrix
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarDividedPolynomial
open ProximityGap.ApolarRootTransition ProximityGap.ApolarMomentCoordinates
open ProximityGap.ApolarCoordinateEquations

namespace ArkLib.ProximityGap.Frontier.ApolarGenericCoprime

/-- A trivial rectangular polynomial kernel persists over every extension
field of the fraction field, by a surviving maximal-column minor. -/
theorem kernel_map {R E I J : Type*} [CommRing R] [IsDomain R] [Field E]
    [Fintype I] [Fintype J] (φ : R →+* E) (hi : Function.Injective φ)
    (M : Matrix I J R) (hm : ∀ v, M *ᵥ v=0 → v=0)
    (x : J → E) (hx : (M.map φ) *ᵥ x=0) : x=0 := by
  classical
  by_contra hn
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hn
  let η := algebraMap R (FractionRing R)
  obtain ⟨rows,_,hdet⟩ := AGL24.exists_square_submatrix_det_ne_zero (M.map η)
    (AGL24.frac_kernel_trivial_of_poly_kernel_trivial M hm)
  let Q := M.submatrix rows id
  have hmul : (Q.map φ) *ᵥ x = 0 := funext fun i => congrFun hx (rows i)
  have hsing := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hmul
    (i:=j) (mem_nonZeroDivisors_of_ne_zero hj)
  have hzero : Q.det=0 := by
    apply hi
    rw [map_zero,RingHom.map_det]
    exact hsing
  apply hdet
  change (Q.map η).det = 0
  rw [← RingHom.mapMatrix_apply,← RingHom.map_det,hzero,map_zero]

/-- Minimality through the preceding homogeneous degree persists in any
field receiving an injective map from the integral coefficient ring. -/
theorem minimal_map {R E I : Type*} [CommRing R] [IsDomain R] [Field E]
    (D : Finset I) (y w : I → R) (φ : R →+* E) (hi : Function.Injective φ) (r b : ℕ)
    (hmin : ∀ p : R[X], p.natDegree ≤ r → ApolarThrough (measure D y w) p b → p=0)
    (p : E[X]) (hp : p.natDegree ≤ r) (ha : ApolarThrough (measure D (φ ∘ y) (φ ∘ w)) p b) :
    p = 0 := by
  classical
  let A := measure D y w
  let N := measure D (φ ∘ y) (φ ∘ w)
  let m (j : ℕ) := A (X^j)
  let m' (j : ℕ) := N (X^j)
  let M : Matrix (Fin (b+1)) (Fin (r+1)) R := fun j i => m (j.val+i.val)
  have hkernel (v : Fin (r+1) → R) (hv : M *ᵥ v=0) : v=0 := by
    have he : ApolarThrough (functional m) (form v) b := by
      apply (equations_iff_apolar m v).mp
      intro j hj
      exact congrFun hv ⟨j,by omega⟩
    have hzero := hmin (form v) (form_degree v) (by simpa only [m,functional_moments,A] using he)
    funext i
    simpa only [coeff_form,coeff_zero,Pi.zero_apply] using congrArg (fun q : R[X] => q.coeff i.val) hzero
  let v (i : Fin (r+1)) := p.coeff i.val
  have hpform : form v=p := form_coeff _ hp
  have he := (equations_iff_apolar m' v).mpr (by simpa only [m',functional_moments,hpform,N] using ha)
  have hmap (j : ℕ) : m' j=φ (m j) := by
    simpa only [m',m,N,A,Polynomial.map_pow,Polynomial.map_X] using measure_map D y w φ (X^j)
  have hv : (M.map φ) *ᵥ v = 0 := by
    funext j
    have hh := he j.val (by have := j.isLt;omega)
    simp only [hmap] at hh
    exact hh
  have hz := kernel_map φ hi M hkernel v hv
  rw [← hpform,hz]
  simp [form]

/-- For arbitrary finite sites and affine or higher polynomial weights, integral
minimality implies generic coprimality over the parameter fraction field. -/
theorem generic_coprime {R J I : Type*} [CommRing R] [IsDomain R] [Field J]
    [Algebra R J] [IsFractionRing R J] (D : Finset I) (y w : I → R)
    (f : R[X]) (r s : ℕ) (hf : f.natDegree = r+1)
    (ha : ApolarThrough (measure D y w) f s)
    (hmin : ∀ q : R[X], q.natDegree ≤ r → ApolarThrough (measure D y w) q (s+1) → q=0) :
    IsCoprime (f.map (algebraMap R J)) ((representative D y w f).map (algebraMap R J)) := by
  classical
  let E := AlgebraicClosure J
  let ι := algebraMap R J
  let τ := algebraMap J E
  let φ := τ.comp ι
  have hinj : Function.Injective φ := τ.injective.comp (IsFractionRing.injective R J)
  let N := measure D (φ ∘ y) (φ ∘ w)
  have hnd : (f.map φ).natDegree=r+1 := (natDegree_map_eq_of_injective hinj f).trans hf
  have hap : ApolarThrough N (f.map φ) s := apolar_map D y w φ f s ha
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed J E _ _).mpr
  intro x
  by_cases hx : (f.map φ).IsRoot x
  · right
    have hn := divided_nonzero N (f.map φ) x hnd hx hap (fun q hdeg hne hq =>
      hne (minimal_map D y w φ hinj r (s+1) hmin q hdeg.le hq))
    rw [aeval_def,← eval_map,Polynomial.map_map]
    change ((representative D y w f).map φ).eval x ≠ 0
    rw [map_representative,eval_representative]
    exact hn
  · left
    rw [aeval_def,← eval_map,Polynomial.map_map]
    exact hx

#print axioms generic_coprime

end ArkLib.ProximityGap.Frontier.ApolarGenericCoprime
