/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.GenericDifferentialFunctionField
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.IsSepClosed

/-! # Extending the scalar derivation to a separable closure

The scalar function field may be imperfect. A separable extension is formally
étale, so its identity lifts along the projection of the dual numbers with
their base algebra structure twisted by the prescribed first derivative.
-/

set_option autoImplicit false
noncomputable section
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.SeparableScalarDifferential

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Differential K]

/-- A separable algebraic extension carries a differential agreeing with the
given one on the base field, also in prime characteristic. -/
theorem exists_extension [Algebra.IsSeparable K L] :
    ∃ d : Differential L, letI := d; ∀ x : K, (algebraMap K L x)′ = algebraMap K L x′ := by
  let j := GenericDifferentialFunctionField.ringJet K L
  letI : Algebra K (TrivSqZeroExt L L) := j.toAlgebra
  let π : TrivSqZeroExt L L →ₐ[K] L :=
    { (TrivSqZeroExt.fstHom L L L).toRingHom with commutes' := fun _ => rfl }
  have sur : Function.Surjective π := fun x => ⟨⟨x,0⟩,rfl⟩
  have nil : IsNilpotent (RingHom.ker π.toRingHom) := ⟨2, TrivSqZeroExt.kerIdeal_sq L L⟩
  letI := Algebra.FormallyEtale.of_isSeparable K L
  let η := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K L) π sur nil
  have fst (x : L) : (η x).fst = x :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id K L) π sur nil x
  let ds := ((TrivSqZeroExt.sndHom L L).toAddMonoidHom.comp η.toRingHom.toAddMonoidHom).toIntLinearMap
  let d : Differential L := ⟨Derivation.mk' ds (fun x y => by
    change (η (x*y)).snd = x*(η y).snd+y*(η x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul]
    change (η x).fst*(η y).snd+(η x).snd*(η y).fst = _
    rw [fst, fst]; ring)⟩
  refine ⟨d,fun x => ?_⟩
  exact congrArg TrivSqZeroExt.snd (η.commutes x)

/-- The absolute separable closure is a valid coefficient field for the
projective cubic formal sheets and their coefficientwise derivatives. -/
theorem closure_extension :
    ∃ d : Differential (SeparableClosure K), letI := d
      ∀ x : K, (algebraMap K (SeparableClosure K) x)′ = algebraMap K (SeparableClosure K) x′ :=
  exists_extension K (SeparableClosure K)

#print axioms exists_extension
#print axioms closure_extension
end ArkLib.ProximityGap.Frontier.SeparableScalarDifferential
