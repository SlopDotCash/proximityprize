/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarRootTransition
import ArkLib.Research.ProximityGap.Frontier.ApolarChartDescent

/-! # The coordinate transition from the two literal interpolation identities -/

set_option autoImplicit false
open Finset Polynomial
namespace ProximityGap.ApolarCoordinateEquations
open ApolarDividedLocator ApolarDividedPolynomial ApolarRootTransition ApolarChartDescent

variable {R A ι : Type*} [CommRing R] [CommRing A]

theorem measure_map (D : Finset ι) (y w : ι → R) (φ : R →+* A) (q : R[X]) :
    measure D (φ ∘ y) (φ ∘ w) (q.map φ) = φ (measure D y w q) := by
  simp only [ApolarRootTransition.measure,LinearMap.sum_apply,LinearMap.smul_apply,Polynomial.leval,smul_eq_mul,
    map_sum,map_mul,Function.comp_apply]
  apply sum_congr rfl
  intro i hi
  change φ (w i) * (q.map φ).eval (φ (y i)) = φ (w i) * φ (q.eval (y i))
  rw [eval_map,eval₂_at_apply]

/-- Apolarity of a finite weighted functional persists under arbitrary base change,
including passage to a nonreduced generic locator quotient. -/
theorem apolar_map (D : Finset ι) (y w : ι → R) (φ : R →+* A) (f : R[X]) (s : ℕ)
    (ha : ApolarThrough (measure D y w) f s) :
    ApolarThrough (measure D (φ ∘ y) (φ ∘ w)) (f.map φ) s := by
  intro z hz
  apply Polynomial.induction_with_natDegree_le
    (fun p => measure D (φ ∘ y) (φ ∘ w) (f.map φ*p) = 0) s (by simp) _ _ z hz
  · intro j a _ hj
    have hh := congrArg φ (ha (X^j) ((natDegree_X_pow_le j).trans hj))
    rw [← measure_map,Polynomial.map_mul,Polynomial.map_pow,map_X,map_zero] at hh
    rw [← mul_assoc,mul_comm (f.map φ),mul_assoc,← smul_eq_C_mul,map_smul,hh,smul_zero]
  · intro p q _ _ hp hq
    rw [mul_add,map_add,hp,hq,zero_add]

variable [Nontrivial A]

/-- Coordinate inversion compares two interpolation decompositions at an arbitrary power
in the universal root algebra. -/
theorem power_equations (power : ℕ) (D : Finset ι) (y : ι → Rˣ) (w : ι → R)
    (f V B B' Q Q' : R[X]) (s : R) (φ : R →+* A) (x : Aˣ) {r k n : ℕ}
    (hk : 0 < k) (hf : f.natDegree ≤ r + 1) (hV : V.natDegree ≤ n)
    (hx : (f.map φ).IsRoot (x:A)) (hs : IsUnit (φ s))
    (ha : ApolarThrough (measure D (fun i => (y i:R)) w) f (k-1))
    (h0 : V*(representative D (fun i => (y i:R)) w f)^power = f*Q+C s*B)
    (h1 : reflect n V*(-representative D (fun i => (↑(y i)⁻¹:R))
      (fun i => w i*(y i:R)^(r+k)) (reflect (r+1) f))^power =
      reflect (r+1) f*Q'+C s*B') :
    (x:A)^n*(B'.map φ).eval (↑x⁻¹:A) = (x:A)^((k+1)* power)*(B.map φ).eval (x:A) := by
  let z (i : ι) := Units.map φ.toMonoidHom (y i)
  obtain ⟨v,hv⟩ := hs
  have hfm := (natDegree_map_le (p := f) (f := φ)).trans hf
  apply power_remainders power D z (φ ∘ w) x v (f.map φ) (V.map φ) _ _ hk hfm hx
      (apolar_map D (fun i => (y i:R)) w φ f (k-1) ha) (natDegree_map_le.trans hV)
  · have h := congrArg (fun p : R[X] => (p.map φ).eval (x:A)) h0
    simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_C,
      eval_mul,eval_pow,eval_add,eval_C,hx.eq_zero,zero_mul,zero_add,map_representative] at h
    rw [hv]
    exact h.symm
  · have hfx : (reflect (r+1) (f.map φ)).eval (↑x⁻¹:A) = 0 := by
      simp only [eval_reflect x⁻¹ _ _ hfm,inv_inv,hx.eq_zero,mul_zero]
    have h := congrArg (fun p : R[X] => (p.map φ).eval (↑x⁻¹:A)) h1
    simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_C,
      Polynomial.map_neg,← reflect_map,eval_mul,eval_pow,eval_add,eval_C,hfx,zero_mul,zero_add,
      map_representative] at h
    have hw : (fun i => (φ ∘ w) i*(z i:A)^(r+k)) = φ ∘ (fun i => w i*(y i:R)^(r+k)) := by
      funext i
      change φ (w i)*(φ (y i:R))^(r+k) = φ (_*_)
      rw [map_mul,map_pow]
    rw [hv,hw]
    exact h.symm

/-- A projective-coordinate comparison built directly from two polynomial
decompositions of the cubed divided representative. -/
theorem coordinate_equations (D : Finset ι) (y : ι → Rˣ) (w : ι → R)
    (f V B B' Q Q' : R[X]) (s : R) (φ : R →+* A) (x : Aˣ) {r k n : ℕ}
    (hk : 0 < k) (hf : f.natDegree ≤ r + 1) (hV : V.natDegree ≤ n)
    (hx : (f.map φ).IsRoot (x:A)) (hs : IsUnit (φ s))
    (ha : ApolarThrough (measure D (fun i => (y i:R)) w) f (k-1))
    (h0 : V*(representative D (fun i => (y i:R)) w f)^3 = f*Q+C s*B)
    (h1 : reflect n V*(-representative D (fun i => (↑(y i)⁻¹:R))
      (fun i => w i*(y i:R)^(r+k)) (reflect (r+1) f))^3 =
      reflect (r+1) f*Q'+C s*B') :
    (x:A)^n*(B'.map φ).eval (↑x⁻¹:A) = (x:A)^((k+1)*3)*(B.map φ).eval (x:A) :=
  power_equations 3 D y w f V B B' Q Q' s φ x hk hf hV hx hs ha h0 h1

/-- Clear the coordinate transition for any power of the divided representative in the
bivariate ring. -/
theorem power_congruence (power : ℕ) {K J : Type*} [Field K] [IsAlgClosed K]
    (D : Finset J) (y : J → K[X]ˣ) (w : J → K[X]) (f V B B' Q Q' : K[X][X]) (s : K[X])
    {r k n m b c : ℕ} (hk : 0 < k) (hf : f.natDegree ≤ r + 1) (hV : V.natDegree ≤ n)
    (hnodes : ∀ t : K, f.map (evalRingHom t) ≠ 0) (hzero : f.coeff 0 ≠ 0) (hs : s ≠ 0)
    (hm : B'.natDegree ≤ m) (htwist : b + (k+1)* power = n + c)
    (ha : ApolarThrough (ApolarRootTransition.measure D (fun i => (y i:K[X])) w) f (k-1))
    (h0 : V*(representative D (fun i => (y i:K[X])) w f)^power = f*Q+C s*B)
    (h1 : reflect n V*(-representative D (fun i => (↑(y i)⁻¹:K[X]))
      (fun i => w i*(y i:K[X])^(r+k)) (reflect (r+1) f))^power =
      reflect (r+1) f*Q'+C s*B') :
    Bivariate.swap f ∣ C (X^b) *
        ArkLib.ProximityGap.Frontier.ApolarReciprocalCharts.reverseCoeffs m (Bivariate.swap B') -
        C (X^(m+c)) * Bivariate.swap B := by
  let L := FractionRing K[X]
  let φ := algebraMap K[X] L
  let F := f.map φ
  apply descend_compare (L := L) f B B' m b (m+c) hnodes
  change AdjoinRoot.root F ^ b * AdjoinRoot.mk F ((reflect m B').map φ) =
    AdjoinRoot.root F ^ (m+c) * AdjoinRoot.mk F (B.map φ)
  rcases subsingleton_or_nontrivial (AdjoinRoot F) with hsub | hnon
  · exact Subsingleton.elim _ _
  let ψ := (AdjoinRoot.of F).comp φ
  have hinj := IsFractionRing.injective K[X] L
  have hF0 : F.eval 0 ≠ 0 := by
    change (f.map φ).eval 0 ≠ 0
    rw [← coeff_zero_eq_eval_zero,coeff_map]
    exact (map_ne_zero_iff φ hinj).mpr hzero
  obtain ⟨x,hx⟩ := unit_root F hF0
  have hroot : (f.map ψ).IsRoot (x:AdjoinRoot F) := by
    rw [hx]
    simpa only [F,Polynomial.map_map,ψ] using AdjoinRoot.isRoot_root F
  have hs' : IsUnit (ψ s) := ((map_ne_zero_iff φ hinj).mpr hs).isUnit.map (AdjoinRoot.of F)
  have h := power_equations power D y w f V B B' Q Q' s ψ x hk hf hV hroot hs' ha h0 h1
  have hclear := clear_twist x (B.map ψ) (B'.map ψ) (natDegree_map_le.trans hm) htwist h
  have hv (q : K[X][X]) : (q.map ψ).eval (x:AdjoinRoot F) = AdjoinRoot.mk F (q.map φ) := by
    rw [hx,show q.map ψ = (q.map φ).map (AdjoinRoot.of F) from (Polynomial.map_map φ _ q).symm,
      eval_map]
    exact AdjoinRoot.aeval_eq (q.map φ)
  rw [reflect_map,hv,hv,hx] at hclear
  exact hclear

/-- The cleared coordinate congruence for the actual cubic interpolation
remainders. Both sides lie in the original bivariate polynomial ring. -/
theorem coordinate_congruence {K J : Type*} [Field K] [IsAlgClosed K]
    (D : Finset J) (y : J → K[X]ˣ) (w : J → K[X]) (f V B B' Q Q' : K[X][X]) (s : K[X])
    {r k n m b c : ℕ} (hk : 0 < k) (hf : f.natDegree ≤ r + 1) (hV : V.natDegree ≤ n)
    (hnodes : ∀ t : K, f.map (evalRingHom t) ≠ 0) (hzero : f.coeff 0 ≠ 0) (hs : s ≠ 0)
    (hm : B'.natDegree ≤ m) (htwist : b + (k+1)*3 = n + c)
    (ha : ApolarThrough (ApolarRootTransition.measure D (fun i => (y i:K[X])) w) f (k-1))
    (h0 : V*(representative D (fun i => (y i:K[X])) w f)^3 = f*Q+C s*B)
    (h1 : reflect n V*(-representative D (fun i => (↑(y i)⁻¹:K[X]))
      (fun i => w i*(y i:K[X])^(r+k)) (reflect (r+1) f))^3 =
      reflect (r+1) f*Q'+C s*B') :
    Bivariate.swap f ∣ C (X^b) *
        ArkLib.ProximityGap.Frontier.ApolarReciprocalCharts.reverseCoeffs m (Bivariate.swap B') -
        C (X^(m+c)) * Bivariate.swap B :=
  power_congruence 3 D y w f V B B' Q Q' s hk hf hV hnodes hzero hs hm htwist ha h0 h1

#print axioms coordinate_congruence
#print axioms apolar_map
#print axioms coordinate_equations
end ProximityGap.ApolarCoordinateEquations
