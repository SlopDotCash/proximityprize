/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarSyndromeInterpolation
import ArkLib.Research.ProximityGap.Frontier.ApolarRootTransition

/-! # Cubic interpolation from sparse specialized moments in any projective chart -/

set_option autoImplicit false
open Polynomial Finset
namespace ProximityGap.ApolarSparseInterpolation
open ApolarDividedLocator ApolarDividedPolynomial ApolarSyndromeInterpolation
open ArkLib.ProximityGap.Frontier.ApolarFiberInterpolation
variable {K R : Type*} [Field K] [CommRing R]

private theorem map_moment (H : Finset K) (w : K → K) (φ : K →+* R) (j : ℕ) :
    weighted H φ w (X^j) = φ (weighted H (RingHom.id K) w (X^j)) := by
  simp [weighted_apply]

/-- Agreement of all bounded moments persists in any coefficient algebra. -/
theorem lift_agreement (H E : Finset K) (w v : K → K) (φ : K →+* R) {d : ℕ}
    (he : ∀ p : K[X], p.natDegree ≤ d →
      weighted H (RingHom.id K) w p = weighted E (RingHom.id K) v p)
    (p : R[X]) (hp : p.natDegree ≤ d) : weighted H φ w p = weighted E φ v p := by
  apply Polynomial.induction_with_natDegree_le
    (fun p => weighted H φ w p = weighted E φ v p) d (by simp) _ _ p hp
  · intro j c _ hj
    rw [← smul_eq_C_mul,map_smul,map_smul,map_moment H w φ,map_moment E v φ,
      he _ ((natDegree_X_pow_le j).trans hj)]
  · intro p q _ _ hp hq
    rw [map_add,map_add,hp,hq]

/-- The divisor relation only requires an equality of moments on a sparse fiber.
It also applies to coordinate-transformed weights and parameter reciprocals. -/
theorem sparse_dvd (H E : Finset K) (w v : K → K) (f : K[X]) {d s : ℕ}
    (hE : E ⊆ H) (hc : E.card ≤ s+1) (hf : f.natDegree+s ≤ d)
    (hrep : ∀ p : K[X], p.natDegree ≤ d →
      weighted H (RingHom.id K) w p = weighted E (RingHom.id K) v p)
    (ha : ApolarThrough (weighted H (RingHom.id K) w) f s) :
    f ∣ Lagrange.nodal H id * representative H id w f := by
  have he : ApolarThrough (weighted E (RingHom.id K) v) f s := by
    intro p hp
    rw [← hrep _ (natDegree_mul_le.trans (by omega)),ha _ hp]
  apply AdjoinRoot.mk_eq_zero.mp
  rw [← AdjoinRoot.aeval_eq,aeval_def,eval₂_mul,eval₂_representative]
  rcases subsingleton_or_nontrivial (AdjoinRoot f) with hsub | hnon
  · exact Subsingleton.elim _ _
  have hd : (divided (f.map (AdjoinRoot.of f)) (AdjoinRoot.root f)).natDegree ≤ d := by
    rw [divided,natDegree_divByMonic _ (monic_X_sub_C _),natDegree_X_sub_C]
    have hh := natDegree_map_le (p := f) (f := AdjoinRoot.of f)
    omega
  rw [AdjoinRoot.algebraMap_eq,lift_agreement H E w v (AdjoinRoot.of f) hrep _ hd]
  convert quotient_reduced_fiber H E v f hE hc he using 1
  simp [Lagrange.nodal,eval₂_finsetProd,eval_prod,AdjoinRoot.algebraMap_eq]

/-- Both interpolation polynomials are obtained from the pencil and its sparse
fibers. A multiple of the domain vanisher clears every multiplicity. -/
theorem interpolate (H G : Finset K) (w : K → K[X]) (V : K[X]) (f : K[X][X])
    {l d s : ℕ} (hG : G.Nonempty) (hV : Lagrange.nodal H id ∣ V)
    (hw : ∀ i ∈ H, (w i).natDegree ≤ 1) (hf : ∀ j, (f.coeff j).natDegree ≤ l)
    (hdeg : f.natDegree+s ≤ d) (hm : 3*(l+1) < G.card+l)
    (hsp : ∀ t ∈ G, ∃ E ⊆ H, E.card ≤ s+1 ∧ ∃ v : K → K, ∀ p : K[X], p.natDegree ≤ d →
      weighted H (RingHom.id K) (fun i => (w i).eval t) p = weighted E (RingHom.id K) v p)
    (ha : ∀ t ∈ G, ApolarThrough (weighted H (RingHom.id K) (fun i => (w i).eval t))
      (f.map (evalRingHom t)) s) :
    ∃ Q B : K[X][X],
      C V * (Bivariate.swap (representative H C w f))^3 =
        Bivariate.swap f * Q + Lagrange.nodal G C * B ∧ Q.natDegree < G.card ∧
        (B = 0 ∨ B.natDegree < l) := by
  classical
  let P := Bivariate.swap (representative H C w f)
  have hp : P.natDegree ≤ l+1 := degree_swap _ _ (pencil_coefficient_degree H w f l hw hf)
  apply interpolate_fiber_quotients G hG (Bivariate.swap f) (C V*P^3) l (degree_swap f l hf)
  · have hd := (natDegree_C_mul_le V (P^3)).trans (natDegree_pow_le (p := P) (n := 3))
    omega
  · intro t ht
    obtain ⟨E,hE,hc,v,hrep⟩ := hsp t ht
    have hd := natDegree_map_le (p := f) (f := evalRingHom t)
    have hh := sparse_dvd H E (fun i => (w i).eval t) v (f.map (evalRingHom t))
      hE hc (by omega) hrep (ha t ht)
    obtain ⟨W,hW⟩ := hV
    let T := representative H id (fun i => (w i).eval t) (f.map (evalRingHom t))
    change (Bivariate.swap f).eval (C t) ∣ (C V*P^3).eval (C t)
    rw [eval_swap,eval_mul,eval_pow,eval_C,show P = _ from rfl,eval_swap,map_representative]
    have hsite : (evalRingHom t) ∘ (C : K →+* K[X]) = id := by funext i; simp
    rw [hsite,hW]
    change _ ∣ (Lagrange.nodal H id*W)*T^3
    convert hh.mul_right (W*T^2) using 1
    dsimp only [T]
    ring

#print axioms lift_agreement
#print axioms sparse_dvd
#print axioms interpolate
end ProximityGap.ApolarSparseInterpolation
