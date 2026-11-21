/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarMomentCoordinates

/-! # Parameter degree of a minimal apolar locator -/

open Polynomial Finset Matrix
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarCoordinateTransport
open ProximityGap.ApolarMomentCoordinates ProximityGap.ApolarHankelMinors
open ProximityGap.ApolarPrimitiveKernel

namespace ProximityGap.ApolarMinimalDegree

variable {K : Type*} [Field K]

/-- The first nonzero apolar degree and its coprime endpoint coefficients bound
the parameter degree for any pencil of affine moments. -/
theorem degree_of_apolar (L : K[X][X] →ₗ[K[X]] K[X]) (f : K[X][X]) {d r : ℕ}
    (hr : r+1 ≤ d) (hlen : 2*r ≤ d) (hf : f.natDegree ≤ r+1)
    (hcop : IsCoprime (f.coeff (r+1)) (f.coeff 0)) (htop : f.coeff (r+1) ≠ 0)
    (hker : ApolarThrough L f (d-(r+1)))
    (hmin : ∀ p : K[X][X], p.natDegree ≤ r → ApolarThrough L p (d-r) → p=0)
    (hdeg : ∀ j ≤ d, (L (X^j)).natDegree ≤ 1) :
    (d-2*r)*(f.coeff (r+1)).natDegree ≤ r+1 := by
  classical
  let m (j : ℕ) := L (X^j)
  let v (k : ℕ) (i : Fin (r+1)) := m (k+i.val)
  let c (i : Fin (r+1)) := f.coeff i.val
  let z := f.coeff (r+1)
  let a := d-2*r
  have hfull : ∀ j ≤ d-(r+1), ∑ i : Fin ((r+1)+1), m (j+i.val) * f.coeff i.val = 0 := by
    apply (equations_iff_apolar m _).mpr
    rw [form_coeff f hf]
    simpa only [m,functional_moments] using hker
  have hrec (j : ℕ) (hj : j < a) : ∑ i, c i • v (j+i.val) = (-z) • v (j+r+1) := by
    funext b
    have hb := b.isLt
    have h := hfull (j+b.val) (by dsimp only [a] at hj; omega)
    rw [Fin.sum_univ_castSucc] at h
    simp only [Fin.val_castSucc,Fin.val_last] at h
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    dsimp only [c,v,z]
    rw [neg_mul]
    apply eq_neg_of_add_eq_zero_left
    convert h using 2
    · apply sum_congr rfl
      intro i _
      rw [mul_comm]
      congr 1
      exact congrArg m (by omega)
    · rw [mul_comm]
      congr 1
      exact congrArg m (by omega)
  have hinj (p : Fin (r+1) → K[X]) (h : ∀ k < a+r+1, v k ⬝ᵥ p=0) : p=0 := by
    have he : ApolarThrough (functional m) (form p) (d-r) := by
      apply (equations_iff_apolar m p).mp
      intro j hj
      exact h j (by dsimp only [a]; omega)
    have hp := hmin (form p) (form_degree _) (by simpa only [m,functional_moments] using he)
    funext i
    simpa only [coeff_form,coeff_zero,Pi.zero_apply] using congrArg (fun q : K[X][X] => q.coeff i.val) hp
  have hn := first_minor_ne_zero v c htop hrec hinj
  have hdiv := endpoint_dvd v c z a hrec
  have hc : IsCoprime z (c 0) := hcop
  have hd := natDegree_le_of_dvd (hc.pow.dvd_of_dvd_mul_left hdiv) hn
  rw [natDegree_pow] at hd
  have hh := Polynomial.natDegree_det_le (block v 0) (B:=1) (by
    intro i j
    apply hdeg
    have hi := i.isLt
    have hj := j.isLt
    omega)
  exact hd.trans (by simpa using hh)

/-- An affine moment pencil and its least kernel in a primitive full-degree
chart satisfy the parameter-degree inequality over the base polynomial ring. -/
theorem chart_evaluation_degree (m : ℕ → K[X]) {d r : ℕ} (hr : r+1 ≤ d)
    (hlen : 2*r ≤ d) (hm : ∀ j ≤ d, (m j).natDegree ≤ 1)
    (w : Fin ((r+1)+1) → K[X]) (hw : catalecticant m d (r+1) *ᵥ w = 0)
    (hmin : ∀ p : Fin (r+1) → K[X], catalecticant m d r *ᵥ p = 0 → p=0)
    (x z : K) (hxz : x ≠ z) (hc : IsCoprime ((family w).map (evalRingHom x))
      ((family w).map (evalRingHom z))) :
    (d-2*r)*((family w).map (evalRingHom z)).natDegree ≤ r+1 := by
  classical
  by_cases hzero : ((family w).map (evalRingHom z)).natDegree=0
  · simp [hzero]
  let g := substitute (r+1) (C (C z)*X-C (C x)) (X-1) (form w)
  let L := (functional m).comp (substitute d (X-C (C x)) (X-C (C z)))
  have hxc : (C x : K[X]) ≠ C z := fun he => hxz (C_injective he)
  obtain ⟨h₀,h₁⟩ := transformed_endpoints K w x z
  change g.coeff 0 = _ at h₀
  change g.coeff (r+1) = _ at h₁
  have hdegG : g.natDegree ≤ r+1 := by
    apply substitute_degree _ _ _ _ _ (form_degree w) <;> compute_degree
  have htop : g.coeff (r+1) ≠ 0 := by
    intro he
    apply hzero
    rw [← h₁,he,natDegree_zero]
  have hcop : IsCoprime (g.coeff (r+1)) (g.coeff 0) := by
    rw [h₀,h₁,isCoprime_mul_unit_left_right ((isUnit_one.neg).pow (r+1))]
    exact hc.symm
  have hold : ApolarThrough (functional m) (form w) (d-(r+1)) := by
    apply (equations_iff_apolar m _).mp
    intro j hj
    exact congrFun hw ⟨j, by omega⟩
  have hker : ApolarThrough L g (d-(r+1)) := by
    have hh := (apolar_substitute_iff (C x) (C z) hxc (functional m) (form w)
      (s:=d-(r+1)) (form_degree _)).mpr hold
    simpa only [Nat.add_sub_of_le hr] using hh
  have hprev (p : K[X][X]) (hp : p.natDegree ≤ r) (ha : ApolarThrough (functional m) p (d-r)) :
      p=0 := by
    let b (i : Fin (r+1)) := p.coeff i.val
    have hpb : form b = p := form_coeff p hp
    have he := (equations_iff_apolar m b).mpr (by rwa [hpb])
    have hb := hmin b (funext fun i => he i.val (by have := i.isLt; omega))
    rw [←hpb,hb]
    simp [form]
  have htr := (trivial_kernel_iff (C x) (C z) hxc (functional m) r (d-r)).mp hprev
  have hi : ∀ q : K[X][X], q.natDegree ≤ r → ApolarThrough L q (d-r) → q=0 := by
    simpa only [Nat.add_sub_of_le (show r ≤ d by omega)] using htr
  have hh := degree_of_apolar L g hr hlen hdegG hcop htop hker hi
    (functional_chart_degree m hm x z)
  rwa [h₁] at hh

/-- An affine moment pencil and its least kernel in a primitive full-degree
chart satisfy the parameter-degree inequality over the base polynomial ring. -/
theorem minimal_chart_degree (m : ℕ → K[X]) {d r : ℕ} (hr : r+1 ≤ d)
    (hlen : 2*r ≤ d) (hm : ∀ j ≤ d, (m j).natDegree ≤ 1)
    (w : Fin ((r+1)+1) → K[X]) (hw : catalecticant m d (r+1) *ᵥ w = 0)
    (hmin : ∀ p : Fin (r+1) → K[X], catalecticant m d r *ᵥ p = 0 → p=0)
    (x z : K) (hxz : x ≠ z) (ht : ((family w).map (evalRingHom z)).natDegree =
      (family w).natDegree) (hc : IsCoprime ((family w).map (evalRingHom x))
      ((family w).map (evalRingHom z))) :
    (d-2*r)*(family w).natDegree ≤ r+1 := by
  simpa only [ht] using chart_evaluation_degree m hr hlen hm w hw hmin x z hxz hc

open Code
open scoped NNReal

/-- The actual MCA bad parameters give a primitive, least-degree locator with the
determinantal parameter degree bound. The degree-zero locator case is retained. -/
theorem degree_of_mca_events {F L ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Field L] [IsAlgClosed L] [Infinite L] [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (φ : F →+* L) (dom : ι ↪ F) {k e d : ℕ} {δ : ℝ≥0}
    (u : WordStack F (Fin 2) ι) (bad : Finset F) (hs : e+1 < bad.card)
    (hed : e ≤ d) (hlen : 2*e ≤ d+2) (hk : 1 ≤ k) (hd : k+d < Fintype.card ι)
    (he : Fintype.card ι - e ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊)
    (hbad : ∀ t ∈ bad, mcaEvent (ReedSolomon.code dom k : Set (ι → F)) δ (u 0) (u 1) t)
    (avoid : Finset L) :
    let H := (univ : Finset ι).map dom
    let μ := fun j => (moment H (ApolarMcaSyndrome.coordinateRow dom (u 0))
      (ApolarMcaSyndrome.coordinateRow dom (u 1)) j).map φ
    ∃ s ≤ e, ∃ w : Fin (s+1) → L[X], w ≠ 0 ∧ catalecticant μ d s *ᵥ w = 0 ∧
      (∀ t : L, (family w).eval (C t) ≠ 0) ∧
      (∀ q < s, ∀ p : Fin (q+1) → L[X], catalecticant μ d q *ᵥ p = 0 → p = 0) ∧
      (s=0 ∨ (d+2-2*s)*(family w).natDegree ≤ s) := by
  classical
  obtain ⟨s,hse,hmin,w,hw,hk0,hprim,x,_,z,_,hxz,_,ht,hcop⟩ :=
    minimal_chart_of_mca_events φ dom u bad hs hed hk hd he hbad avoid
  refine ⟨s,hse,w,hw,hk0,hprim,hmin,?_⟩
  cases s with
  | zero => exact Or.inl rfl
  | succ r =>
    right
    have hh := minimal_chart_degree _ (d:=d) (r:=r) (by omega) (by omega) (by
      intro j _
      unfold moment
      simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_X,Polynomial.map_C]
      compute_degree) w hk0 (hmin r (by omega)) x z hxz ht hcop
    simpa only [show d+2-2*(r+1)=d-2*r by omega] using hh

#print axioms degree_of_mca_events
#print axioms minimal_chart_degree
#print axioms degree_of_apolar

end ProximityGap.ApolarMinimalDegree
