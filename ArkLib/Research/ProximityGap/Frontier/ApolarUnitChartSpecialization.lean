/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarUnitChartData

/-! # Sparse scalar fibers in the two parameter charts -/

open Polynomial Finset
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarRootTransition
open ProximityGap.ApolarSparseSpecialization ProximityGap.ApolarUnitChartData

namespace ProximityGap.ApolarUnitChartSpecialization

variable {K : Type*} [Field K]

/-- Specializing the full polynomial-weight measure agrees exactly with the
scalar weighted measure on the specialized test polynomial. -/
theorem specialize_measure (D : Finset K) (w : K → K[X]) (t : K) (p : K[X][X]) :
    ((measure D (C : K → K[X]) w) p).eval t =
      weighted D (RingHom.id K) (fun y => (w y).eval t) (p.map (evalRingHom t)) := by
  simp only [ApolarRootTransition.measure,LinearMap.sum_apply,LinearMap.smul_apply,Polynomial.leval,
    LinearMap.coe_mk,AddHom.coe_mk,smul_eq_mul,eval_finsetSum,eval_mul,eval_commute,
    weighted_apply,RingHom.id_apply]

/-- The specialization formula for a test polynomial over the constant field. -/
theorem specialize_measure_const (D : Finset K) (w : K → K[X]) (t : K) (p : K[X]) :
    ((measure D (C : K → K[X]) w) (p.map C)).eval t =
      weighted D (RingHom.id K) (fun y => (w y).eval t) p := by
  have h : (evalRingHom t).comp (C : K →+* K[X]) = RingHom.id K := RingHom.ext fun a => eval_C
  rw [specialize_measure,Polynomial.map_map,h,Polynomial.map_id]

/-- Polynomial-pencil apolarity specializes at every scalar, with no restriction
on the rank or the specialized degree. -/
theorem specialize_apolar (D : Finset K) (w : K → K[X]) (f : K[X][X]) (s : ℕ)
    (h : ApolarThrough (measure D (C : K → K[X]) w) f s) (t : K) :
    ApolarThrough (weighted D (RingHom.id K) (fun y => (w y).eval t))
      (f.map (evalRingHom t)) s := by
  intro B hb
  have he := congrArg (Polynomial.eval t) (h (B.map C) (natDegree_map_le.trans hb))
  have hc : (evalRingHom t).comp (C : K →+* K[X]) = RingHom.id K := RingHom.ext fun a => eval_C
  simpa only [specialize_measure,Polynomial.map_mul,Polynomial.map_map,hc,Polynomial.map_id,eval_zero] using he

/-- Reciprocal evaluation of an affine polynomial weight rescales it by the
reciprocal parameter. -/
theorem reciprocal_affine (w : K[X]) (hw : w.natDegree ≤ 1) (t : K) (ht : t ≠ 0) :
    (reflect 1 w).eval t⁻¹ = t⁻¹*w.eval t := by
  let _ := invertibleOfNonzero ht
  have h := eval₂_reflect_mul_pow (RingHom.id K) t 1 w hw
  simp only [invOf_eq_inv,eval₂_id,pow_one] at h
  apply (mul_right_cancel₀ ht)
  simpa only [mul_right_comm _ (w.eval t) t,inv_mul_cancel₀ ht,one_mul] using h

/-- Uniform scalar rescaling preserves a sparse representation of every moment.
At reciprocal parameters the error sites are identical. -/
theorem reciprocal_sparse (H E : Finset K) (w : K → K[X]) (v : K → K) {d : ℕ}
    (hw : ∀ y ∈ H, (w y).natDegree ≤ 1) (t : K) (ht : t ≠ 0)
    (hs : ∀ p : K[X], p.natDegree ≤ d → weighted H (RingHom.id K) (fun i => (w i).eval t) p =
      weighted E (RingHom.id K) v p) (p : K[X]) (hp : p.natDegree ≤ d) :
    weighted H (RingHom.id K) (fun i => (reflect 1 (w i)).eval t⁻¹) p =
      weighted E (RingHom.id K) (fun i => t⁻¹*v i) p := by
  have h := congrArg (fun x : K => t⁻¹*x) (hs p hp)
  simp only [weighted_apply,RingHom.id_apply,Finset.mul_sum] at h ⊢
  convert h using 1
  · apply sum_congr rfl
    intro i hi
    rw [reciprocal_affine _ (hw _ hi) _ ht,mul_assoc]
  · apply sum_congr rfl
    intro i _
    rw [mul_assoc]

/-- Sparse fiber families pass unchanged through reciprocal parameters, for
arbitrary affine polynomial weights and independent of the chart construction. -/
theorem reciprocal_sparse_family [DecidableEq K] (H G : Finset K) (w : K → K[X]) (d b : ℕ)
    (h0 : 0 ∉ G) (hw : ∀ y ∈ H, (w y).natDegree ≤ 1)
    (hsp : ∀ t ∈ G, ∃ E ⊆ H, E.card ≤ b ∧ ∃ v : K → K, ∀ p : K[X], p.natDegree ≤ d →
      weighted H (RingHom.id K) (fun i => (w i).eval t) p = weighted E (RingHom.id K) v p) :
    ∀ z ∈ G.image Inv.inv, ∃ E ⊆ H, E.card ≤ b ∧ ∃ v : K → K, ∀ p : K[X], p.natDegree ≤ d →
      weighted H (RingHom.id K) (fun i => (reflect 1 (w i)).eval z) p =
        weighted E (RingHom.id K) v p := by
  intro z hz
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hz
  obtain ⟨E,hE,hn,v,hv⟩ := hsp t ht
  exact ⟨E,hE,hn,fun i => t⁻¹*v i,reciprocal_sparse H E w v hw t
    (fun h => h0 (h ▸ ht)) hv⟩

variable [DecidableEq K] {H S : Finset K} {e d r l : ℕ}

/-- Sparse-fiber input to interpolation on the original parameter chart. -/
theorem interpolation_sparse (A : Data H S e d r l) (he : e ≤ d-r+1) :
    ∀ t ∈ A.G, ∃ E ⊆ A.D, E.card ≤ d-r+1 ∧ ∃ v : K → K, ∀ p : K[X], p.natDegree ≤ d →
      weighted A.D (RingHom.id K) (fun i => (A.w i).eval t) p = weighted E (RingHom.id K) v p := by
  intro t ht
  obtain ⟨E,hE,hn,v,hsp,_⟩ := A.sparse t ht
  exact ⟨E,hE,hn.trans he,v,fun p hp => (specialize_measure_const A.D A.w t p).symm.trans (hsp p hp)⟩

/-- Sparse-fiber input on the reciprocal parameter chart, with the specialized
weights of the actual reversed polynomial pencil. -/
theorem reciprocal_interpolation_sparse (A : Data H S e d r l) (he : e ≤ d-r+1) :
    ∀ z ∈ A.G.image Inv.inv, ∃ E ⊆ A.D, E.card ≤ d-r+1 ∧ ∃ v : K → K, ∀ p : K[X], p.natDegree ≤ d →
      weighted A.D (RingHom.id K) (fun i => (reflect 1 (A.w i)).eval z) p =
        weighted E (RingHom.id K) v p := by
  exact reciprocal_sparse_family A.D A.G A.w d (d-r+1) A.parameters_unit A.weights_affine
    (interpolation_sparse A he)

/-- The global normalized apolarity provides the local hypothesis at every
selected parameter on the original chart. -/
theorem interpolation_apolar (A : Data H S e d r l) (t : K) :
    ApolarThrough (weighted A.D (RingHom.id K) (fun y => (A.w y).eval t))
      (A.f.map (evalRingHom t)) (d-r) :=
  specialize_apolar A.D A.w A.f (d-r) A.apolar t

/-- The numerical bidegree and interpolation inequalities for the rate-half
predecessor in length 4h. The two coordinate exponents are strictly separated. -/
theorem half_shape {h r l M : ℕ} (hr : r ≤ h-1) (hrpos : 0<r) (hl : 0<l)
    (hdet : (2*h-1+2-2*r)*l ≤ r) (hcount : h+2<M) :
    3*l ≤ r ∧ 3*(l+1)<M ∧ (4*h-3*(2*h-1+2-r)) < r ∧
      h-1 ≤ 2*h-1-r+1 ∧ r+(2*h-1-r)=2*h-1 ∧ 1<r := by
  have hthree : 3 ≤ 2*h-1+2-2*r := by omega
  have hrank := (Nat.mul_le_mul_right l hthree).trans hdet
  omega

#print axioms reciprocal_sparse_family
#print axioms reciprocal_interpolation_sparse
#print axioms specialize_apolar
#print axioms interpolation_sparse
#print axioms half_shape

end ProximityGap.ApolarUnitChartSpecialization
