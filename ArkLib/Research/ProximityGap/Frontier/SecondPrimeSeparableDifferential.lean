/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-! # Extension of a differential to a separable algebraic field extension -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeSeparableDifferential

open scoped Differential
open TrivSqZeroExt
variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Differential K]

private noncomputable def baseMap : K →+* TrivSqZeroExt E E where
  toFun a := (algebraMap K E a, algebraMap K E a′)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by
    ext
    · exact map_add _ _ _
    · change algebraMap K E (a+b)′ = algebraMap K E a′ + algebraMap K E b′
      rw [map_add, map_add]
  map_mul' a b := by
    ext
    · exact map_mul _ _ _
    · change algebraMap K E ((a*b)′) = algebraMap K E a * algebraMap K E b′ +
        algebraMap K E a′ * algebraMap K E b
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul]
      rw [mul_comm (algebraMap K E b)]

/-- A derivation extends over every separable algebraic extension, including an infinite
separable closure in positive characteristic. Lift the identity through the square-zero
dual numbers with the base algebra structure twisted by its given differential. -/
theorem exists_differential [Algebra.IsSeparable K E] :
    ∃ d : Differential E, letI := d; DifferentialAlgebra K E := by
  classical
  let B := TrivSqZeroExt E E
  let _ : Algebra K B := (baseMap (K := K) (E := E)).toAlgebra
  let π : B →ₐ[K] E := { (fstHom E E E).toRingHom with commutes' := fun _ => rfl }
  have hπ : Function.Surjective π := fun x => ⟨(x, 0), rfl⟩
  have hn : IsNilpotent (RingHom.ker π) :=
    ⟨2, TrivSqZeroExt.kerIdeal_sq E E⟩
  let _ : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  let Ψ := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K E) π hπ hn
  have proj (x : E) : (Ψ x).fst = x :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id K E) π hπ hn x
  let L : E →+ E := (sndHom E E).toAddMonoidHom.comp Ψ.toRingHom.toAddMonoidHom
  let d : Differential E := ⟨Derivation.mk' L.toIntLinearMap (by
    intro x y
    change (Ψ (x*y)).snd = x • (Ψ y).snd + y • (Ψ x).snd
    rw [map_mul, snd_mul, proj, proj]
    simp [mul_comm])⟩
  refine ⟨d, ⟨?_⟩⟩
  intro x
  change (Ψ (algebraMap K E x)).snd = _
  exact congrArg TrivSqZeroExt.snd (Ψ.commutes x)

/-- Chosen differential on a separable extension, with its base compatibility. -/
@[instance_reducible] noncomputable def extension [Algebra.IsSeparable K E] : Differential E :=
  Classical.choose (exists_differential (K := K) (E := E))

theorem compatible [Algebra.IsSeparable K E] :
    letI := extension (K := K) (E := E)
    DifferentialAlgebra K E :=
  Classical.choose_spec (exists_differential (K := K) (E := E))

#print axioms compatible
end ArkLib.ProximityGap.Frontier.SecondPrimeSeparableDifferential
