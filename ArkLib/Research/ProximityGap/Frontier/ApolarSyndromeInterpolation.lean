/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarDividedPolynomial
import ArkLib.Research.ProximityGap.Frontier.ApolarFiberInterpolation
import ArkLib.Research.ProximityGap.Frontier.ApolarReciprocalCharts

/-! # Interpolation of the cubic divided syndrome of an actual pair of words -/

set_option autoImplicit false
open Finset Polynomial
namespace ProximityGap.ApolarSyndromeInterpolation
open ApolarDividedLocator ApolarDividedPolynomial
open ArkLib.ProximityGap.Frontier.ApolarFiberInterpolation
open ArkLib.ProximityGap.Frontier.ApolarReciprocalCharts
variable {K : Type*} [Field K]

/-- The coordinate polynomial after exchanging variables is the parameter specialization. -/
theorem eval_swap (f : K[X][X]) (t : K) :
    (Bivariate.swap f).eval (C t) = f.map (evalRingHom t) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add,eval_add,Polynomial.map_add,hf,hg]
  | monomial n a =>
    rw [Bivariate.swap_monomial,eval_mul,eval_C,eval_map,eval₂_at_apply,map_monomial,
      C_mul_X_pow_eq_monomial]
    rfl

/-- A bound on all coefficient degrees controls the parameter after exchange. -/
theorem degree_swap (f : K[X][X]) (l : ℕ) (hf : ∀ i, (f.coeff i).natDegree ≤ l) :
    (Bivariate.swap f).natDegree ≤ l := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  ext i
  simpa only [swap_coeff,coeff_zero] using coeff_eq_zero_of_natDegree_lt ((hf i).trans_lt hj)

noncomputable def pencil (H : Finset K) (u v : K → K) (f : K[X][X]) : K[X][X] :=
  representative H C (fun x => C (rowWeight H u x)+X*C (rowWeight H v x)) f

/-- Interpolate on the entire bad family using the cubic of the concrete syndrome.
The resulting parameter degree of the remainder is strictly below the locator's. -/
theorem interpolate_neighbors (H G : Finset K) (u v : K → K) (f : K[X][X])
    {l s : ℕ} (hG : G.Nonempty) (hf : ∀ j, (f.coeff j).natDegree ≤ l)
    (hm : 3*(l+1)<G.card+l)
    (hclose : ∀ t ∈ G, ∃ E ⊆ H, ∃ Q : K[X], E.card ≤ s+1 ∧
      (∀ x ∈ H, x ∉ E → u x+t*v x = Q.eval x) ∧
      Q.natDegree + (f.map (evalRingHom t)).natDegree + s < H.card-1)
    (ha : ∀ t ∈ G, ApolarThrough (syndrome H (RingHom.id K) (fun x => u x+t*v x))
      (f.map (evalRingHom t)) s) :
    let U := C (Lagrange.nodal H id) * (Bivariate.swap (pencil H u v f))^3
    ∃ Q B : K[X][X], U = Bivariate.swap f * Q + Lagrange.nodal G C * B ∧
      Q.natDegree < G.card ∧ (B=0 ∨ B.natDegree < l) := by
  classical
  let P := Bivariate.swap (pencil H u v f)
  have hP : P.natDegree ≤ l+1 := by
    apply degree_swap
    apply pencil_coefficient_degree _ _ _ _ _ hf
    intro i _
    apply (natDegree_add_le _ _).trans
    rw [max_le_iff]
    exact ⟨by simp, (natDegree_mul_le).trans (by simp)⟩
  apply interpolate_fiber_quotients G hG (Bivariate.swap f)
      (C (Lagrange.nodal H id)*P^3) l (degree_swap f l hf)
  · have hd := (natDegree_C_mul_le (Lagrange.nodal H id) (P^3)).trans
      (natDegree_pow_le (p := P) (n := 3))
    omega
  · intro t ht
    obtain ⟨E,hE,Q,hc,hoff,hd⟩ := hclose t ht
    have h := fiber_dvd H E (fun x => u x+t*v x) Q (f.map (evalRingHom t)) hE hoff hc hd (ha t ht)
    change (Bivariate.swap f).eval (C t) ∣ (C (Lagrange.nodal H id)*P^3).eval (C t)
    rw [eval_swap,eval_mul,eval_C,eval_pow,show P = _ from rfl,eval_swap,
      pencil,specialize_syndrome_pencil]
    convert h.mul_right ((representative H id (rowWeight H (fun x => u x+t*v x))
      (f.map (evalRingHom t)))^2) using 1
    ring

#print axioms eval_swap
#print axioms interpolate_neighbors
end ProximityGap.ApolarSyndromeInterpolation
