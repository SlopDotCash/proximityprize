/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic.Ring

/-! # Derivations of fraction fields and separable simple extensions

The first-order map `r ↦ (r, Dr)` takes values in the dual numbers. It extends
to the fraction field because the first coordinate of each nonzero denominator
is a unit. On an irreducible simple extension with nonzero value derivative, the
implicit derivative gives a well-defined derivation of the quotient.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Differential nonZeroDivisors

namespace ArkLib.ProximityGap.Frontier.GenericDifferentialFunctionField

section Fraction
variable (R K : Type*) [CommRing R] [IsDomain R] [Differential R] [Field K]
    [Algebra R K] [IsFractionRing R K]

private def ringJet : R →+* TrivSqZeroExt K K where
  toFun a := ⟨algebraMap R K a, algebraMap R K a′⟩
  map_one' := by
    apply Prod.ext
    · exact map_one _
    · change algebraMap R K (1 : R)′ = 0
      simp
  map_zero' := by
    apply Prod.ext
    · exact map_zero _
    · change algebraMap R K (0 : R)′ = 0
      simp
  map_add' a b := by
    apply Prod.ext
    · exact map_add _ _ _
    · change algebraMap R K ((a+b)′) = algebraMap R K a′ + algebraMap R K b′
      rw [map_add, map_add]
  map_mul' a b := by
    apply Prod.ext
    · exact map_mul _ _ _
    · change algebraMap R K ((a*b)′) =
        algebraMap R K a * algebraMap R K b′ + algebraMap R K a′ * algebraMap R K b
      rw [Differential.deriv.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
      ring

private theorem ringJet_unit (z : R⁰) : IsUnit (ringJet R K z) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  apply isUnit_iff_ne_zero.mpr
  change algebraMap R K z ≠ 0
  exact (IsFractionRing.injective R K).ne (nonZeroDivisors.ne_zero z.property) |>.trans_eq
    (map_zero _)

private def fractionJet : K →+* TrivSqZeroExt K K := IsLocalization.lift (M := R⁰) (ringJet_unit R K)

private theorem fractionJet_base (r : R) : fractionJet R K (algebraMap R K r) = ringJet R K r :=
  IsLocalization.lift_eq _ _

private theorem fractionJet_fst (a : K) : (fractionJet R K a).fst = a := by
  have he : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (fractionJet R K) = RingHom.id K := by
    apply IsLocalization.ringHom_ext R⁰
    ext r
    change (fractionJet R K (algebraMap R K r)).fst = algebraMap R K r
    rw [fractionJet_base]
    rfl
  exact RingHom.congr_fun he a

/-- The extension of a base differential to an arbitrary fraction field. -/
@[instance_reducible] def fractionDifferential : Differential K :=
  ⟨Derivation.mk'
    (((TrivSqZeroExt.sndHom K K).toAddMonoidHom.comp (fractionJet R K).toAddMonoidHom).toIntLinearMap)
    (fun a b => by
      change (fractionJet R K (a*b)).snd = a*(fractionJet R K b).snd + b*(fractionJet R K a).snd
      rw [map_mul, TrivSqZeroExt.snd_mul]
      change (fractionJet R K a).fst * (fractionJet R K b).snd +
          (fractionJet R K a).snd * (fractionJet R K b).fst = _
      rw [fractionJet_fst, fractionJet_fst]
      ring)⟩

/-- The first-order fraction map restricts on the base ring to its prescribed derivative. -/
theorem fraction_deriv_algebraMap (r : R) :
    letI := fractionDifferential R K
    (algebraMap R K r)′ = algebraMap R K r′ :=
  congrArg TrivSqZeroExt.snd (fractionJet_base R K r)

end Fraction

section Adjoint
variable {K : Type*} [Field K] [Differential K]
variable (f : K[X]) [Fact (Irreducible f)] (hreg : f.derivative ≠ 0)

omit [Differential K] in
include hreg in
private theorem root_derivative_ne : AdjoinRoot.mk f f.derivative ≠ 0 := by
  intro hz
  exact hreg (dvd_derivative_iff.mp (AdjoinRoot.mk_eq_zero.mp hz))

private def liftVelocity : K[X] := Classical.choose (AdjoinRoot.mk_surjective
  (-AdjoinRoot.mk f (Differential.mapCoeffs f) / AdjoinRoot.mk f f.derivative))

private theorem liftVelocity_spec : AdjoinRoot.mk f (liftVelocity f) =
    -AdjoinRoot.mk f (Differential.mapCoeffs f) / AdjoinRoot.mk f f.derivative :=
  Classical.choose_spec (AdjoinRoot.mk_surjective _)

/-- Extend the differential across a simple irreducible equation with nonzero
value derivative. The equation need not be monic and the characteristic may be positive. -/
@[instance_reducible] def adjointDifferential (hreg : f.derivative ≠ 0) : Differential (AdjoinRoot f) where
  deriv := Derivation.liftOfSurjective (f := (AdjoinRoot.mk f).toIntAlgHom)
    AdjoinRoot.mk_surjective (d := Differential.implicitDeriv (liftVelocity f)) (by
      rintro x hx
      simp only [RingHom.toIntAlgHom_apply, AdjoinRoot.mk_eq_zero] at hx ⊢
      obtain ⟨q,rfl⟩ := hx
      simp only [Derivation.leibniz, smul_eq_mul]
      apply dvd_add (dvd_mul_right ..)
      apply dvd_mul_of_dvd_right
      rw [← AdjoinRoot.mk_eq_zero]
      unfold Differential.implicitDeriv
      simp only [Derivation.coe_add, Derivation.coe_smul, Pi.add_apply, Pi.smul_apply,
        Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul, map_add, map_mul,
        liftVelocity_spec]
      rw [div_mul_cancel₀ _ (root_derivative_ne f hreg), add_neg_cancel])

set_option backward.isDefEq.respectTransparency false in
/-- The differential on the simple extension agrees with the differential on its base. -/
theorem adjoint_deriv_algebraMap (a : K) :
    letI := adjointDifferential f hreg
    (algebraMap K (AdjoinRoot f) a)′ = algebraMap K (AdjoinRoot f) a′ := by
  change (Derivation.liftOfSurjective _ _) ((AdjoinRoot.mk f).toIntAlgHom (C a)) = _
  rw [Derivation.liftOfSurjective_apply, Differential.implicitDeriv_C]
  rfl

end Adjoint

end ArkLib.ProximityGap.Frontier.GenericDifferentialFunctionField

open ArkLib.ProximityGap.Frontier.GenericDifferentialFunctionField in
#print axioms fraction_deriv_algebraMap
open ArkLib.ProximityGap.Frontier.GenericDifferentialFunctionField in
#print axioms adjoint_deriv_algebraMap
