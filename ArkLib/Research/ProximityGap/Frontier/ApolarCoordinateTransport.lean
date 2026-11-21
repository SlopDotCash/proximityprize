/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarDividedLocator
import Mathlib.Algebra.Polynomial.Homogenize

/-! # Projective coordinate change for apolar moments -/

open Polynomial Finset
namespace ProximityGap.ApolarCoordinateTransport

variable {R : Type*} [CommRing R]

/-- Substitute an affine numerator and denominator into a degree-n binary form. -/
noncomputable def substitute (n : ℕ) (N D : R[X]) : R[X] →ₗ[R] R[X] :=
  (MvPolynomial.aeval ![N,D]).toLinearMap.comp (homogenizeLM n)

theorem substitute_mul (N D p q : R[X]) {r s : ℕ}
    (hp : p.natDegree ≤ r) (hq : q.natDegree ≤ s) :
    substitute (r+s) N D (p*q) = substitute r N D p * substitute s N D q := by
  simp only [substitute,LinearMap.comp_apply,AlgHom.toLinearMap_apply,homogenizeLM_apply,
    homogenize_mul p q hp hq,map_mul]

theorem substitute_term (N D : R[X]) (a : R) {j s : ℕ} (hj : j ≤ s) :
    substitute s N D (C a*X^j) = C a*N^j*D^(s-j) := by
  simp only [substitute, LinearMap.comp_apply, AlgHom.toLinearMap_apply, homogenizeLM_apply,
    homogenize_C_mul, homogenize_X_pow hj, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  change C a * (N^j * D^(s-j)) = _
  ring

theorem substitute_degree (N D p : R[X]) {s : ℕ} (hN : N.natDegree ≤ 1)
    (hD : D.natDegree ≤ 1) (hp : p.natDegree ≤ s) :
    (substitute s N D p).natDegree ≤ s := by
  apply Polynomial.induction_with_natDegree_le (fun q => (substitute s N D q).natDegree ≤ s) s
    (by simp) _ _ p hp
  · intro j a _ hj
    rw [substitute_term _ _ _ hj]
    apply (natDegree_mul_le (p := C a*N^j) (q := D^(s-j))).trans
    have h1 := natDegree_C_mul_le a (N^j)
    have h2 := (natDegree_pow_le (p := N) (n := j)).trans (Nat.mul_le_mul_left j hN)
    have h3 := (natDegree_pow_le (p := D) (n := s-j)).trans (Nat.mul_le_mul_left (s-j) hD)
    omega
  · intro f g _ _ hf hg
    rw [map_add]
    exact natDegree_add_le_of_degree_le hf hg

/-- The last coefficient of the transformed binary form is its value at the second chart point. -/
theorem top_coefficient (x z : R) (p : R[X]) {s : ℕ} (hp : p.natDegree ≤ s) :
    (substitute s (C z*X-C x) (X-1) p).coeff s = p.eval z := by
  let U : R[X] := C z*X-C x
  let V : R[X] := X-1
  have hU : U.natDegree ≤ 1 := by dsimp [U]; compute_degree
  have hV : V.natDegree ≤ 1 := by dsimp [V]; compute_degree
  have hu : U.coeff 1 = z := by simp [U,coeff_sub]
  have hv : V.coeff 1 = 1 := by simp [V,coeff_sub,coeff_one]
  apply Polynomial.induction_with_natDegree_le (fun B => (substitute s U V B).coeff s = B.eval z) s
    (by simp) _ _ p hp
  · intro j a ha hj
    rw [substitute_term _ _ _ hj, mul_assoc,coeff_C_mul]
    have hd₁ : (U^j).natDegree ≤ j := by simpa using (natDegree_pow_le_of_le j hU)
    have hd₂ : (V^(s-j)).natDegree ≤ s-j := by simpa using (natDegree_pow_le_of_le (s-j) hV)
    have hprod := coeff_mul_add_eq_of_natDegree_le hd₁ hd₂
    rw [Nat.add_sub_of_le hj] at hprod
    rw [hprod]
    have hw₁ : (U^j).coeff j = U.coeff 1 ^j := by simpa only [Nat.mul_one] using (coeff_pow_of_natDegree_le (m := j) hU)
    have hw₂ : (V^(s-j)).coeff (s-j) = V.coeff 1 ^(s-j) := by
      simpa only [Nat.mul_one] using (coeff_pow_of_natDegree_le (m := s-j) hV)
    simp [hw₁,hw₂,hu,hv]
  · intro f g _ _ hf hg
    simp only [map_add,coeff_add,eval_add,hf,hg]

/-- The first coefficient is its value at the first chart point, up to the uniform sign. -/
theorem bottom_coefficient (x z : R) (p : R[X]) {s : ℕ} (hp : p.natDegree ≤ s) :
    (substitute s (C z*X-C x) (X-1) p).coeff 0 = (-1)^s*p.eval x := by
  apply Polynomial.induction_with_natDegree_le (fun B => (substitute s (C z*X-C x) (X-1) B).coeff 0 =
      (-1)^s*B.eval x) s (by simp) _ _ p hp
  · intro j a _ hj
    rw [substitute_term _ _ _ hj, coeff_zero_eq_eval_zero]
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_one, mul_zero,zero_sub]
    rw [show -x = (-1)*x by ring, mul_pow]
    have h : (-1:R)^j * (-1)^(s-j) = (-1)^s := by rw [← pow_add,Nat.add_sub_of_le hj]
    rw [← h]
    ring
  · intro f g _ _ hf hg
    simp only [map_add,coeff_add,eval_add,hf,hg,mul_add]

/-- Pullback of the parameter pencil commutes with forming affine combinations. -/
theorem pencil_substitute (A B : R[X] →ₗ[R] R) (t : R) (N D : R[X]) (s : ℕ) :
    (A+t • B).comp (substitute s N D) =
      A.comp (substitute s N D) + t • B.comp (substitute s N D) := rfl

variable {K : Type*} [Field K]

/-- Evaluation at a point where the denominator is nonzero gives the usual
fractional-linear evaluation, with the homogeneous denominator power. -/
theorem eval_substitute (N D p : K[X]) {s : ℕ} (hp : p.natDegree ≤ s) (y : K)
    (hD : D.eval y ≠ 0) :
    (substitute s N D p).eval y = p.eval (N.eval y / D.eval y) * D.eval y ^s := by
  let ψ := evalRingHom y
  have he : ψ.comp (C : K →+* K[X]) = RingHom.id _ := by ext x; simp [ψ]
  change ψ (MvPolynomial.eval₂Hom C ![N,D] (p.homogenize s)) = _
  rw [MvPolynomial.map_eval₂Hom, he]
  change MvPolynomial.eval (fun i => ψ (![N,D] i)) (p.homogenize s) = _
  exact eval_homogenize hp (fun i => ψ (![N,D] i)) hD

theorem substitute_C_mul (N D : R[X]) (s : ℕ) (a : R) (p : R[X]) :
    substitute s N D (C a*p) = C a * substitute s N D p := by
  simp only [← smul_eq_C_mul,map_smul]

private theorem substitute_one (N D : R[X]) (s : ℕ) :
    substitute s N D 1 = D^s := by
  simpa using substitute_term N D (1:R) (Nat.zero_le s)

private theorem substitute_linear_pow (N D P : R[X]) (hP : P.natDegree ≤ 1) (j : ℕ) :
    substitute j N D (P^j) = (substitute 1 N D P)^j := by
  induction j with
  | zero => simp [substitute_one]
  | succ j ih =>
    rw [pow_succ, substitute_mul N D _ _ (by simpa using natDegree_pow_le_of_le j hP) hP,
      ih, pow_succ]

/-- Composition as a binary substitution identity, valid over arbitrary coefficient rings. -/
theorem substitute_comp (A B N D p : R[X]) {s : ℕ} (hN : N.natDegree ≤ 1)
    (hD : D.natDegree ≤ 1) (hp : p.natDegree ≤ s) :
    substitute s A B (substitute s N D p) =
      substitute s (substitute 1 A B N) (substitute 1 A B D) p := by
  apply Polynomial.induction_with_natDegree_le (fun q => substitute s A B (substitute s N D q) =
      substitute s (substitute 1 A B N) (substitute 1 A B D) q) s (by simp) _ _ p hp
  · intro j a _ hj
    rw [substitute_term _ _ _ hj, substitute_term _ _ _ hj, mul_assoc,substitute_C_mul]
    have hprod := substitute_mul A B (N^j) (D^(s-j)) (r:=j) (s:=s-j)
      (by simpa using natDegree_pow_le_of_le j hN) (by simpa using natDegree_pow_le_of_le (s-j) hD)
    rw [Nat.add_sub_of_le hj] at hprod
    rw [hprod, substitute_linear_pow _ _ _ hN, substitute_linear_pow _ _ _ hD, mul_assoc]
  · intro g q _ _ hg hq
    simp only [map_add,hg,hq]

private theorem substitute_scale (c : R) (p : R[X]) {s : ℕ} (hp : p.natDegree ≤ s) :
    substitute s (C c * X) (C c) p = c^s • p := by
  apply Polynomial.induction_with_natDegree_le (fun q => substitute s (C c*X) (C c) q =
      c^s • q) s (by simp) _ _ p hp
  · intro j a _ hj
    rw [substitute_term _ _ _ hj, mul_pow,smul_eq_C_mul, map_pow]
    have hcp : (C c)^j * (C c)^(s-j) = (C c)^s := by rw [← pow_add, Nat.add_sub_of_le hj]
    rw [← hcp]
    ring
  · intro g q _ _ hg hq
    simp only [map_add,smul_add,hg,hq]

private theorem substitute_one_linear (A B : R[X]) (a b : R) :
    substitute 1 A B (C a*X-C b) = C a*A-C b*B := by
  have h₁ := substitute_term A B a (show 1 ≤ 1 by decide)
  have h₂ := substitute_term A B b (show 0 ≤ 1 by decide)
  simp only [pow_one, Nat.sub_self, pow_zero, mul_one] at h₁
  simp only [pow_zero,mul_one,Nat.sub_zero,pow_one] at h₂
  rw [map_sub,h₁,h₂]

/-- Reparameterization from two coordinate values, followed by its inverse,
is scaling by the determinant to the homogeneous degree. -/
theorem inverse_substitute (x z : R) (_hxz : x ≠ z) (p : R[X]) {s : ℕ}
    (hp : p.natDegree ≤ s) :
    substitute s (X-C x) (X-C z) (substitute s (C z*X-C x) (X-1) p) = (z-x)^s • p := by
  have hN : (C z*X-C x).natDegree ≤ 1 := by compute_degree
  have hD : ((X:R[X])-1).natDegree ≤ 1 := by compute_degree
  rw [substitute_comp _ _ _ _ _ hN hD hp, substitute_one_linear]
  have hd := substitute_one_linear (X-C x) (X-C z) 1 1
  simp only [map_one,one_mul] at hd
  rw [hd]
  have hn' : C z*(X-C x)-C x*(X-C z) = C (z-x)*X := by rw [map_sub]; ring
  have hd' : (X-C x)-(X-C z)=C (z-x) := by rw [map_sub]; ring
  rw [hn',hd']
  exact substitute_scale (z-x) p hp

/-- Reversing the composition gives the same scalar over any commutative ring. -/
theorem inverse_substitute' (x z : R) (_hxz : x ≠ z) (p : R[X]) {s : ℕ}
    (hp : p.natDegree ≤ s) :
    substitute s (C z*X-C x) (X-1) (substitute s (X-C x) (X-C z) p) = (z-x)^s • p := by
  have hN : ((X:R[X])-C x).natDegree ≤ 1 := by compute_degree
  have hD : ((X:R[X])-C z).natDegree ≤ 1 := by compute_degree
  rw [substitute_comp _ _ _ _ _ hN hD hp]
  have hn := substitute_one_linear (C z*X-C x) (X-1) 1 x
  have hd := substitute_one_linear (C z*X-C x) (X-1) 1 z
  simp only [map_one,one_mul] at hn hd
  rw [hn,hd]
  have hn' : (C z*X-C x)-C x*(X-1)=C (z-x)*X := by rw [map_sub]; ring
  have hd' : (C z*X-C x)-C z*(X-1)=C (z-x) := by rw [map_sub]; ring
  rw [hn',hd']
  exact substitute_scale (z-x) p hp

/-- The catalecticant vanishing conditions are invariant under the coordinate
change, in both directions and in each degree. Here the locus and functional
change in opposite directions. -/
theorem apolar_substitute_iff [IsDomain R] (x z : R) (hxz : x ≠ z) (L : R[X] →ₗ[R] R)
    (f : R[X]) {r s : ℕ} (hf : f.natDegree ≤ r) :
    ApolarDividedLocator.ApolarThrough (L.comp (substitute (r+s) (X-C x) (X-C z)))
      (substitute r (C z*X-C x) (X-1) f) s ↔ ApolarDividedLocator.ApolarThrough L f s := by
  let N : R[X] := X-C x
  let D : R[X] := X-C z
  let U : R[X] := C z*X-C x
  let V : R[X] := X-1
  have hU : U.natDegree ≤ 1 := by dsimp [U]; compute_degree
  have hV : V.natDegree ≤ 1 := by dsimp [V]; compute_degree
  have hN : N.natDegree ≤ 1 := by simp [N]
  have hD : D.natDegree ≤ 1 := by simp [D]
  have hF := substitute_degree U V f hU hV hf
  constructor
  · intro h B hb
    have hB := substitute_degree U V B hU hV hb
    have hh := h (substitute s U V B) hB
    change L (substitute (r+s) N D (substitute r U V f * substitute s U V B)) = 0 at hh
    rw [substitute_mul N D _ _ hF hB, inverse_substitute x z hxz f hf,
      inverse_substitute x z hxz B hb, smul_mul_smul_comm, map_smul, smul_eq_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero
      (pow_ne_zero _ (sub_ne_zero.mpr hxz.symm)) (pow_ne_zero _ (sub_ne_zero.mpr hxz.symm)))
  · intro h B hb
    change L (substitute (r+s) N D (substitute r U V f * B)) = 0
    rw [substitute_mul N D _ _ hF hb, inverse_substitute x z hxz f hf, smul_mul_assoc,
      map_smul,h _ (substitute_degree N D B hN hD hb),smul_zero]

/-- Error support and all of its moments survive the coordinate change; each old
error site has one new site and its weight is rescaled by the denominator power. -/
theorem error_measure_substitute [DecidableEq K] (x z : K) (hxz : x ≠ z) (E : Finset K)
    (hz : z ∉ E) (w : K → K) (d : ℕ) :
    let t := fun y : K => (y-x)/(y-z)
    let inv := fun a : K => (z*a-x)/(a-1)
    let E' := E.image t
    E'.card = E.card ∧ ∀ (p : K[X]), p.natDegree ≤ d →
      ApolarDividedLocator.weighted E (RingHom.id K) w (substitute d (X-C x) (X-C z) p) =
        ApolarDividedLocator.weighted E' (RingHom.id K) (fun a => w (inv a)*(inv a-z)^d) p := by
  classical
  let t := fun y : K => (y-x)/(y-z)
  let inv := fun a : K => (z*a-x)/(a-1)
  have hInv (y : K) (hy : y ∈ E) : inv (t y) = y := by
    have h₁ : y-z ≠ 0 := sub_ne_zero.mpr (fun he => hz (he ▸ hy))
    have h₂ : z-x ≠ 0 := sub_ne_zero.mpr hxz.symm
    have h₃ : t y - 1 = (z-x)/(y-z) := by dsimp [t]; field_simp; ring
    apply (div_eq_iff (h₃ ▸ div_ne_zero h₂ h₁)).mpr
    dsimp [t]
    field_simp
    ring
  have hInj : Set.InjOn t E := fun a ha b hb hab => (hInv a ha).symm.trans ((congrArg inv hab).trans (hInv b hb))
  refine ⟨card_image_of_injOn hInj,?_⟩
  intro p hp
  simp only [ApolarDividedLocator.weighted_apply, RingHom.id_apply]
  rw [sum_image hInj]
  apply sum_congr rfl
  intro y hy
  have h₁ : y-z ≠ 0 := sub_ne_zero.mpr (fun he => hz (he ▸ hy))
  rw [eval_substitute _ _ _ hp y (by simpa using h₁)]
  simp only [eval_X,eval_C,eval_sub]
  change w y * (p.eval (t y) * (y-z)^d) = w (inv (t y)) * (inv (t y)-z)^d * p.eval (t y)
  rw [hInv y hy]
  ring

/-- Triviality of the preceding catalecticant kernel is preserved as well as existence
of an apolar locator. -/
theorem trivial_kernel_iff [IsDomain R] (x z : R) (hxz : x ≠ z) (L : R[X] →ₗ[R] R) (r s : ℕ) :
    (∀ p : R[X], p.natDegree ≤ r → ApolarDividedLocator.ApolarThrough L p s → p = 0) ↔
    (∀ q : R[X], q.natDegree ≤ r →
      ApolarDividedLocator.ApolarThrough (L.comp (substitute (r+s) (X-C x) (X-C z))) q s → q = 0) := by
  let N : R[X] := X-C x
  let D : R[X] := X-C z
  let U : R[X] := C z*X-C x
  let V : R[X] := X-1
  have hU : U.natDegree ≤ 1 := by dsimp [U]; compute_degree
  have hV : V.natDegree ≤ 1 := by dsimp [V]; compute_degree
  have hN : N.natDegree ≤ 1 := by simp [N]
  have hD : D.natDegree ≤ 1 := by simp [D]
  have hc : (z-x)^r ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hxz.symm)
  constructor
  · intro hi q hq ha
    let p := substitute r N D q
    have hp : p.natDegree ≤ r := substitute_degree N D q hN hD hq
    have happ := (apolar_substitute_iff x z hxz L p hp (s:=s)).mp (by
      change ApolarDividedLocator.ApolarThrough _ (substitute r U V (substitute r N D q)) s
      rw [inverse_substitute' x z hxz q hq]
      intro B hb
      rw [smul_mul_assoc,map_smul,ha B hb,smul_zero])
    have he := hi p hp happ
    have hh := congrArg (substitute r U V) he
    change substitute r U V (substitute r N D q) = _ at hh
    rw [inverse_substitute' x z hxz q hq,map_zero] at hh
    exact (smul_eq_zero.mp hh).resolve_left hc
  · intro hi p hp ha
    have hnew := (apolar_substitute_iff x z hxz L p hp (s:=s)).mpr ha
    have hh := congrArg (substitute r N D)
      (hi (substitute r U V p) (substitute_degree U V p hU hV hp) hnew)
    rw [inverse_substitute x z hxz p hp,map_zero] at hh
    exact (smul_eq_zero.mp hh).resolve_left hc

#print axioms trivial_kernel_iff

#print axioms apolar_substitute_iff
#print axioms error_measure_substitute

#print axioms top_coefficient
#print axioms bottom_coefficient
#print axioms substitute_mul
#print axioms inverse_substitute

end ProximityGap.ApolarCoordinateTransport
