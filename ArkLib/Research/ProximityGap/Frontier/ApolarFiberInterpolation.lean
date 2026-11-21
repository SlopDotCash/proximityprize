/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-! # Interpolation of polynomial quotients along scalar fibers

The coefficient domain may itself be a polynomial ring. Divisibility at
distinct scalar nodes supplies a global remainder of small parameter degree.
-/

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.ApolarFiberInterpolation

variable {K R : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]

private theorem nodal_dvd_of_vanishing (s : Finset K) (U : R[X])
    (h : ∀ t ∈ s, U.eval (algebraMap K R t) = 0) :
    Lagrange.nodal s (algebraMap K R) ∣ U := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty => simp
  | @insert a s ha ih =>
    let c := algebraMap K R
    obtain ⟨V, hV⟩ := (Polynomial.dvd_iff_isRoot.mpr
      (h a (Finset.mem_insert_self ..)) : X - C (c a) ∣ U)
    have hs : Lagrange.nodal s c ∣ V := by
      apply ih
      intro t ht
      have hv := h t (Finset.mem_insert_of_mem ht)
      rw [hV, eval_mul, eval_sub, eval_X, eval_C] at hv
      apply (mul_eq_zero.mp hv).resolve_left
      apply sub_ne_zero.mpr
      exact (algebraMap K R).injective.ne (fun hta => ha (hta ▸ ht))
    rw [Lagrange.nodal, Finset.prod_insert ha, hV]
    exact mul_dvd_mul_left _ hs

/-- Interpolate the fiberwise quotients over the scalar field. The result is
valid over any integral coefficient algebra, including \(K[X]\). -/
theorem interpolate_fiber_quotients (s : Finset K) (hs : s.Nonempty)
    (f U : R[X]) (l : ℕ) (hf : f.natDegree ≤ l)
    (hU : U.natDegree < s.card + l)
    (hdiv : ∀ t ∈ s, f.eval (algebraMap K R t) ∣ U.eval (algebraMap K R t)) :
    ∃ Q B : R[X], U = f * Q + Lagrange.nodal s (algebraMap K R) * B ∧
      Q.natDegree < s.card ∧ (B = 0 ∨ B.natDegree < l) := by
  classical
  let c := algebraMap K R
  let q (t : K) : R := if ht : t ∈ s then (hdiv t ht).choose else 0
  let basis (i : K) := (Lagrange.basis s id i).map c
  let Q : R[X] := ∑ i ∈ s, basis i * C (q i)
  have hinj : Set.InjOn (@id K) (s : Set K) := Function.injective_id.injOn
  have hQdeg : Q.natDegree < s.card := by
    have hc := Finset.card_pos.mpr hs
    have hle : Q.natDegree ≤ s.card - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      calc
        (basis i * C (q i)).natDegree ≤ (basis i).natDegree := by
          simpa using (show (basis i * C (q i)).natDegree ≤ (basis i).natDegree + (C (q i)).natDegree from Polynomial.natDegree_mul_le)
        _ ≤ (Lagrange.basis s id i).natDegree := Polynomial.natDegree_map_le
        _ = _ := Lagrange.natDegree_basis hinj hi
    omega
  have hQeval (t : K) (ht : t ∈ s) : Q.eval (c t) = q t := by
    rw [show Q = ∑ i ∈ s, basis i * C (q i) from rfl, Polynomial.eval_finsetSum]
    rw [Finset.sum_eq_single_of_mem t ht]
    · simp only [basis, eval_mul, eval_C, eval_map_apply]
      rw [show (Lagrange.basis s id t).eval t = 1 from
        Lagrange.eval_basis_self hinj ht]
      simp
    · intro j hj hjt
      simp only [basis, eval_mul, eval_C, eval_map_apply]
      rw [show (Lagrange.basis s id j).eval t = 0 from
        Lagrange.eval_basis_of_ne (v := id) hjt ht]
      simp
  have hrem : Lagrange.nodal s c ∣ U - f * Q := by
    apply nodal_dvd_of_vanishing
    intro t ht
    rw [eval_sub, eval_mul, hQeval t ht]
    change U.eval (c t) - f.eval (c t) * q t = 0
    dsimp only [q]
    rw [dite_eq_left ht, ← (hdiv t ht).choose_spec, sub_self]
  obtain ⟨B, hB⟩ := hrem
  refine ⟨Q, B, by rw [← hB]; ring, hQdeg, ?_⟩
  by_cases hzero : B = 0
  · exact Or.inl hzero
  right
  have hnod : Lagrange.nodal s c ≠ 0 := by
    rw [Lagrange.nodal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero (c i)
  have hbound := Polynomial.natDegree_sub_le U (f * Q)
  rw [hB, Polynomial.natDegree_mul hnod hzero, Lagrange.natDegree_nodal] at hbound
  have hmul : (f * Q).natDegree ≤ f.natDegree + Q.natDegree := Polynomial.natDegree_mul_le
  omega

end ArkLib.ProximityGap.Frontier.ApolarFiberInterpolation

#print axioms ArkLib.ProximityGap.Frontier.ApolarFiberInterpolation.interpolate_fiber_quotients
