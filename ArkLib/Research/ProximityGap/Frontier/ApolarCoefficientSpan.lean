/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarAffineKernelSpan
import ArkLib.Research.ProximityGap.Frontier.SharpApolarMCA

/-! # Complete parameter-degree span for a normalized minimal locator -/

set_option autoImplicit false
open Polynomial Finset Matrix
namespace ProximityGap.ApolarCoefficientSpan
open ApolarDividedLocator ApolarDividedPolynomial ApolarRootTransition ApolarMomentCoordinates
open ApolarUnitChartData ApolarChartCancellation ApolarCoordinateEquations
open ArkLib.ProximityGap.Frontier.ApolarGenericCoprime
open ArkLib.ProximityGap.Frontier.ApolarReciprocalCharts

variable {K : Type*} [Field K] [DecidableEq K]

private theorem cross {R I : Type*} [CommRing R] [IsDomain R] [Infinite R]
    (D : Finset I) (y w : I → R) (f q : R[X]) {s : ℕ}
    (hf : f.natDegree ≤ s+1) (hq : q.natDegree ≤ s+1)
    (hfa : ApolarThrough (measure D y w) f s) (hqa : ApolarThrough (measure D y w) q s) :
    q*representative D y w f = f*representative D y w q := by
  apply Polynomial.funext
  intro x
  let L := ApolarRootTransition.measure D y w
  have split (p : R[X]) : C (p.eval x) + (Polynomial.X-C x)*divided p x = p := by
    have h := p.modByMonic_add_div (Polynomial.X-C x)
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at h
    exact h
  have bound (p : R[X]) (h : p.natDegree ≤ s+1) : (divided p x).natDegree ≤ s := by
    rw [divided,natDegree_divByMonic _ (monic_X_sub_C _),natDegree_X_sub_C]
    omega
  have hd : q*divided f x+C (f.eval x)*divided q x =
      f*divided q x+C (q.eval x)*divided f x := by
    linear_combination divided q x * split f - divided f x * split q
  have hh := congrArg L hd
  simp only [map_add,← smul_eq_C_mul,map_smul,smul_eq_mul,
    show L (q*divided f x)=0 from hqa _ (bound f hf),
    show L (f*divided q x)=0 from hfa _ (bound q hq),zero_add] at hh
  simpa only [eval_mul,eval_representative] using hh.symm

omit [DecidableEq K] in
private theorem divides [IsAlgClosed K] (D : Finset K) (w : K → K[X])
    (f q : K[X][X]) {r d : ℕ} (hs : 2*r≤d+1) (hf : f.natDegree=r) (hq : q.natDegree≤r)
    (hfree : ∀ t : K, f.map (evalRingHom t)≠0)
    (hap : ApolarThrough (measure D C w) f (d-r)) (hqa : ApolarThrough (measure D C w) q (d-r))
    (hc : IsCoprime (f.map (algebraMap K[X] (FractionRing K[X])))
      ((representative D C w f).map (algebraMap K[X] (FractionRing K[X])))) : f ∣ q := by
  let φ := algebraMap K[X] (FractionRing K[X])
  apply (primitive_of_no_zero_fiber f hfree).dvd_of_fraction_map_dvd_fraction_map (K:=FractionRing K[X])
  apply hc.dvd_of_dvd_mul_right
  refine ⟨(representative D C w q).map φ,?_⟩
  simpa only [Polynomial.map_mul] using congrArg (Polynomial.map φ)
    (cross D C w f q (by omega) (by omega) hap hqa)

omit [DecidableEq K] in
private theorem moment_affine (D : Finset K) (w : K → K[X]) (hw : ∀ i∈D, (w i).natDegree≤1)
    (j : ℕ) : ((measure D (C : K → K[X]) w) (Polynomial.X^j)).natDegree≤1 := by
  simp only [ApolarRootTransition.measure,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,Polynomial.leval_apply,
    eval_pow,eval_X,← C_pow]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_mul_C_le ..).trans (hw i hi)

/-- The coordinate coefficients of the minimal locator span *all* the
monomials up to its parameter degree, including at rank-deficient fibers. -/
theorem monomials [IsAlgClosed K] {H S : Finset K} {e d r l : ℕ}
    (A : Data H S e d r l) (hr : 0<r) (hl : 0<l) (hs : 2*r≤d+1) (i : ℕ) (hi : i≤l) :
    ∃ c : Fin (r+1) → K, ∑ j, C (c j)*A.f.coeff j.val = Polynomial.X^i := by
  classical
  let L := ApolarRootTransition.measure A.D (C : K → K[X]) A.w
  let m := fun j : ℕ => L (Polynomial.X^j)
  let M : Matrix (Fin (d-r+1)) (Fin (r+1)) K[X] := fun t j => m (t.val+j.val)
  let v (j : Fin (r+1)) := A.f.coeff j.val
  have iff' (b : Fin (r+1) → K[X]) : M *ᵥ b=0 ↔ ApolarThrough L (form b) (d-r) := by
    rw [← functional_moments L,← equations_iff_apolar]
    constructor
    · intro h j hj
      exact congrFun h (⟨j,by omega⟩ : Fin (d-r+1))
    · intro h
      funext j
      exact h j.val (by omega)
  have hv : form v=A.f := form_coeff A.f A.degree.le
  have hc : IsCoprime (A.f.map (algebraMap K[X] (FractionRing K[X])))
      ((representative A.D C A.w A.f).map (algebraMap K[X] (FractionRing K[X]))) := by
    apply generic_coprime A.D (C : K → K[X]) A.w A.f (r-1) (d-r)
      (A.degree.trans (by omega)) A.apolar
    simpa only [show d-r+1=d-(r-1) by omega] using A.minimal (r-1) (by omega)
  apply ApolarAffineKernelSpan.monomials M v hl
    (fun t j => moment_affine A.D A.w A.weights_affine (t.val+j.val))
    ((iff' v).2 (hv ▸ A.apolar)) (fun j => A.height j.val) _ _ i hi
  · intro b hb hsmall
    have div := divides A.D A.w A.f (form b) hs A.degree (form_degree _) A.primitive A.apolar
      ((iff' b).1 hb) hc
    by_contra hne
    have hq : form b≠0 := fun h => hne (funext fun j => (coeff_form b j).symm.trans (by rw [h,coeff_zero];rfl))
    have hs' := natDegree_le_of_dvd (map_dvd Bivariate.swap div)
      (show Bivariate.swap (form b)≠0 by simpa using hq)
    have htop0 : A.f.coeff r≠0 := by intro h; have := A.top_height; rw [h,natDegree_zero] at this; omega
    rw [ApolarCubicObstruction.parameter_degree A.f A.height A.top_height htop0] at hs'
    have hh : (Bivariate.swap (form b)).natDegree < l := by
      apply Nat.lt_of_le_of_lt (ApolarSyndromeInterpolation.degree_swap _ (l-1) ?_) (by omega)
      intro j
      by_cases hj : j<r+1
      · rw [show (form b).coeff j=b ⟨j,hj⟩ from coeff_form b ⟨j,hj⟩]
        have := hsmall ⟨j,hj⟩
        omega
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (form_degree _) (by omega)),natDegree_zero]
        omega
    omega
  · by_contra! hz
    apply A.primitive 0
    ext j
    rw [coeff_map,coeff_zero]
    by_cases hj : j<r+1
    · exact hz ⟨j,hj⟩
    · rw [coeff_eq_zero_of_natDegree_lt (A.degree.trans_lt (by omega)),map_zero]

#print axioms monomials
end ProximityGap.ApolarCoefficientSpan
