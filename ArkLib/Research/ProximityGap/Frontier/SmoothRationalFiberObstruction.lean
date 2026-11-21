/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-! # A third rational fiber after two power-coset fibers with one extra site -/

set_option autoImplicit false
open Finset Polynomial
namespace ArkLib.ProximityGap.Frontier.SmoothRationalFiberObstruction

variable {K : Type*} [Field K] [DecidableEq K]

omit [DecidableEq K] in
/-- Multiplying a fractional linear function by a nonzero factor depending
only on a label permits at most one preimage of a fixed nonzero value per label. -/
theorem third_fiber_injects (E S : Finset K) (q U V : K → K) (a b t : K) (hab : a≠b)
    (hS : ∀ x∈E, q x∈S)
    (hu : ∀ x∈E, U (q x)≠0)
    (heq : ∀ x∈E, U (q x)*(x-a)=t*V (q x)*(x-b)) : E.card≤S.card := by
  apply Finset.card_le_card_of_injOn q hS
  intro x hx y hy hxy
  have ex := heq x hx
  have ey := heq y hy
  rw [← hxy] at ey
  have hne : U (q x)-t*V (q x)≠0 := by
    intro hz
    have hz' := sub_eq_zero.mp hz
    have h' : U (q x)*(x-a)=U (q x)*(x-b) := by rwa [← hz'] at ex
    have : x-a=x-b := mul_left_cancel₀ (hu x hx) h'
    exact hab (by linear_combination -this)
  exact sub_eq_zero.mp ((mul_eq_zero.mp
    (show (U (q x)-t*V (q x))*(x-y)=0 by linear_combination ex - ey)).resolve_left hne)

/-- Let each of two disjoint fibers consist of j whole power-cosets and one
extra site. Any other nonzero finite fiber has at most 2j sites when the
power on the domain has 4j distinct labels. -/
theorem two_padded_cosets (m j : ℕ) (T I J E : Finset K)
    (hT : T.card=4*j) (hI : I.card=j) (hJ : J.card=j) (hi : I⊆T) (hj : J⊆T)
    (hd : Disjoint I J) (a b t : K) (hab : a≠b) (ht : t≠0)
    (hsite : ∀ x∈E, x^m∈T)
    (hnz : ∀ x∈E, (Lagrange.nodal J id).eval (x^m)*(x-b)≠0)
    (hfiber : ∀ x∈E, (Lagrange.nodal I id).eval (x^m)*(x-a)=
      t*((Lagrange.nodal J id).eval (x^m)*(x-b))) : E.card≤2*j := by
  classical
  let S := T \ (I∪J)
  have hs : S.card=2*j := by
    dsimp only [S]
    rw [card_sdiff_of_subset (union_subset hi hj),card_union_of_disjoint hd,hT,hI,hJ]
    omega
  rw [← hs]
  apply third_fiber_injects E S (fun x => x^m) (fun y => (Lagrange.nodal I id).eval y)
    (fun y => (Lagrange.nodal J id).eval y) a b t hab
  · intro x hx
    refine mem_sdiff.mpr ⟨hsite x hx,?_⟩
    intro hmem
    rcases mem_union.mp hmem with hxI | hxJ
    · have hv := Lagrange.eval_nodal_at_node (v:=@id K) hxI
      have h := hfiber x hx
      change (Lagrange.nodal I id).eval (x^m)=0 at hv
      rw [hv,zero_mul] at h
      exact (mul_ne_zero ht (hnz x hx)) h.symm
    · have hv := Lagrange.eval_nodal_at_node (v:=@id K) hxJ
      change (Lagrange.nodal J id).eval (x^m)=0 at hv
      exact hnz x hx (by rw [hv,zero_mul])
  · intro x hx hz
    have h := hfiber x hx
    rw [hz,zero_mul] at h
    exact (mul_ne_zero ht (hnz x hx)) h.symm
  · intro x hx
    simpa only [mul_assoc] using hfiber x hx

/-- For m≥2 and a desired degree mj+1, the third fiber cannot be full. -/
theorem padded_cap_lt (m j : ℕ) (hm : 2≤m) : 2*j<m*j+1 := by
  have := Nat.mul_le_mul_right j hm
  omega

/-- The three-label Parseval bound comes from the sharp comparison at a
single antipodal pair. Each end has either no selected color or one label. -/
theorem color_pair_bound (a b : Fin 4) :
    let s := fun i : Fin 3 => (if a.val=i.val then (1:ℤ) else 0) -
      (if b.val=i.val then (1:ℤ) else 0)
    (s 0-s 1)^2+(s 1-s 2)^2+(s 2-s 0)^2 ≤
      3*((if a.val<3 then (1:ℤ) else 0)+(if b.val<3 then 1 else 0)) := by
  fin_cases a <;> fin_cases b <;> decide

#print axioms third_fiber_injects
#print axioms two_padded_cosets
#print axioms padded_cap_lt
#print axioms color_pair_bound
end ArkLib.ProximityGap.Frontier.SmoothRationalFiberObstruction
