/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Lovett's GM-MDS proof: the F[a] ↔ F(a) base-change bridge (#389)

Lovett's Theorem 1.7 is stated over the rational-function field `F(a)`, but the in-tree
development works over the polynomial ring `F[a] = MvPolynomial (Fin n) F` (avoiding fractions;
arXiv:1803.02523 p.3 remark, "clear denominators").  Lemmas 2.5/2.6 transfer independence by the
substitution-and-divisibility argument over the ring directly, but **Lemma 2.4** uses a field
*basis-counting* step (spanning set of size = dimension is independent), which needs the field.

This file is the bridge: for a family of polynomials over an integral domain `R`, linear
independence over `R` is equivalent to linear independence of the coefficient-mapped family over
`Frac(R)` (`LinearIndependent.iff_fractionRing` composed with the injective coefficient map
`R[X] ↪ Frac(R)[X]`).  Both directions are available, so ring-level bricks lift to the field and
the field-counting arguments come back down.

Issue #389.
-/

open Polynomial

namespace ArkLib.GMMDS

variable {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}

/-- The coefficient-extension `R[X] →ₗ[R] Frac(R)[X]` is injective. -/
theorem mapAlgHom_fractionField_injective :
    Function.Injective
      (fun p : R[X] => p.map (algebraMap R (FractionRing R))) :=
  Polynomial.map_injective _ (IsFractionRing.injective R (FractionRing R))

/-- **Base-change bridge.**  A polynomial family over a domain `R` is `R`-linearly independent iff
its coefficient image is `Frac(R)`-linearly independent. -/
theorem linearIndependent_fractionField_iff (b : ι → R[X]) :
    LinearIndependent R b ↔
      LinearIndependent (FractionRing R)
        (fun i => (b i).map (algebraMap R (FractionRing R))) := by
  set K := FractionRing R
  let f : R[X] →ₗ[R] K[X] := (Polynomial.mapAlgHom (Algebra.ofId R K)).toLinearMap
  have hker : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.mpr mapAlgHom_fractionField_injective
  have hcomp : (fun i => (b i).map (algebraMap R K)) = f ∘ b := rfl
  rw [hcomp, ← LinearMap.linearIndependent_iff f hker]
  exact LinearIndependent.iff_fractionRing R K

end ArkLib.GMMDS

#print axioms ArkLib.GMMDS.linearIndependent_fractionField_iff
