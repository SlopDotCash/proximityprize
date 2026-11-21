/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

/-! # Clearing chart factors in the original bivariate polynomial ring -/
set_option autoImplicit false
open Finset Polynomial
namespace ProximityGap.ApolarChartCancellation

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A factor prime to an individual chart denominator can be cancelled even
when the specialized locator and denominator have no Bézout identity. -/
private theorem cancel_prime {A : Type*} [CommRing A] [IsDomain A] {p f b : A}
    (hp : Prime p) (hn : ¬ p ∣ f) (h : f ∣ p*b) : f ∣ b := by
  obtain ⟨q,hq⟩ := h
  have hd : p ∣ f*q := hq ▸ dvd_mul_right p b
  obtain ⟨v,hv⟩ := (hp.dvd_mul.mp hd).resolve_left hn
  exact ⟨v,mul_left_cancel₀ hp.ne_zero (by rw [hq,hv]; ring)⟩

/-- Divide out the full parameter vanisher using only pointwise nonvanishing
of the locator at the selected fibers. The coefficient ring may be K[X]. -/
theorem cancel_nodal {ι : Type*} (D : Finset ι) (site : ι → R) (f b : R[X])
    (hfree : ∀ i ∈ D, f.eval (site i) ≠ 0)
    (h : f ∣ Lagrange.nodal D site * b) : f ∣ b := by
  classical
  induction D using Finset.induction_on with
  | empty => simpa using h
  | insert i D hi ih =>
    apply ih (fun j hj => hfree j (mem_insert_of_mem hj))
    rw [Lagrange.nodal_insert_eq_nodal hi,mul_assoc] at h
    exact cancel_prime (prime_X_sub_C _) (fun hd =>
      hfree i (mem_insert_self ..) (dvd_iff_isRoot.mp hd)) h

/-- Two interpolation identities and the transition for their numerators imply
the same cleared transition for their remainders in the original ring. -/
theorem compare_nodal {ι : Type*} (D : Finset ι) (site : ι → R)
    (f U V Q Q' B B' a b : R[X]) (hfree : ∀ i ∈ D, f.eval (site i) ≠ 0)
    (hU : U = f*Q + Lagrange.nodal D site*B)
    (hV : V = f*Q' + Lagrange.nodal D site*B')
    (hUV : f ∣ a*V-b*U) : f ∣ a*B'-b*B := by
  apply cancel_nodal D site f _ hfree
  obtain ⟨z,hz⟩ := hUV
  refine ⟨z-a*Q'+b*Q,?_⟩
  rw [hU,hV] at hz
  linear_combination hz

/-- Nonzero fibers over the algebraic closure imply the primitive hypothesis
required to descend divisibility from the generic parameter field. -/
theorem primitive_of_no_zero_fiber {K : Type*} [Field K] [IsAlgClosed K] (f : K[X][X])
    (hf : ∀ t : K, f.map (evalRingHom t) ≠ 0) : f.IsPrimitive := by
  intro p hp
  rw [C_dvd_iff_dvd_coeff] at hp
  by_contra hu
  have hpz : p ≠ 0 := by
    rintro rfl
    apply hf 0
    ext j
    simp [coeff_map, zero_dvd_iff.mp (hp j)]
  have hd := degree_pos_of_ne_zero_of_nonunit hpz hu
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_root p hd.ne'
  apply hf t
  ext j
  obtain ⟨q,hq⟩ := hp j
  simp [coeff_map,hq,ht.eq_zero]

/-- A single identity at the universal root over the parameter fraction field
descends to bivariate polynomial divisibility. -/
theorem descend_root_identity {K L : Type*} [Field K] [IsAlgClosed K]
    [Field L] [Algebra K[X] L] [IsFractionRing K[X] L]
    (f U : K[X][X]) (hf : ∀ t : K, f.map (evalRingHom t) ≠ 0)
    (h : AdjoinRoot.mk (f.map (algebraMap K[X] L)) (U.map (algebraMap K[X] L)) = 0) :
    f ∣ U :=
  (primitive_of_no_zero_fiber f hf).dvd_of_fraction_map_dvd_fraction_map
    (AdjoinRoot.mk_eq_zero.mp h)

#print axioms cancel_nodal
#print axioms compare_nodal
#print axioms descend_root_identity
end ProximityGap.ApolarChartCancellation
