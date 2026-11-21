/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarMinimalDegree

/-! # Removing fixed evaluation sites from a polynomial locator pencil -/

open Finset Polynomial Matrix
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarPrimitiveKernel
open ProximityGap.ApolarMomentCoordinates ProximityGap.ApolarMinimalDegree

namespace ProximityGap.ApolarFixedFactors

variable {K : Type*} [Field K]

/-- A site is fixed if its locator value is identically zero as a parameter polynomial. -/
noncomputable def fixed (H : Finset K) (p : K[X][X]) : Finset K := by
  classical
  exact H.filter fun y => p.eval (C y) = 0

theorem mem_fixed {H : Finset K} {p : K[X][X]} {y : K} :
    y ∈ fixed H p ↔ y ∈ H ∧ p.eval (C y)=0 := by
  classical
  simp [fixed]

/-- Lift the vanisher of the fixed sites to the parameter-polynomial coefficient ring. -/
theorem map_nodal (A : Finset K) :
    (Lagrange.nodal A id).map (C : K →+* K[X]) = Lagrange.nodal A C := by
  classical
  simp [Lagrange.nodal,Polynomial.map_prod,Polynomial.map_sub]

/-- The vanisher of all fixed evaluation sites simultaneously divides the pencil,
and the quotient has no identically vanishing evaluation off these sites. -/
theorem split_fixed (H : Finset K) (p : K[X][X]) (hp : p ≠ 0) :
    let A := fixed H p
    ∃ q : K[X][X], p = (Lagrange.nodal A id).map C * q ∧ q ≠ 0 ∧
      A.card + q.natDegree = p.natDegree ∧
      ∀ y ∈ H, y ∉ A → q.eval (C y) ≠ 0 := by
  classical
  let A := fixed H p
  have hd : Lagrange.nodal A (C : K → K[X]) ∣ p := by
    apply Finset.prod_dvd_of_coprime
    · intro x _ y _ hxy
      apply isCoprime_X_sub_C_of_isUnit_sub
      rw [←map_sub]
      exact ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxy)).map C)
    · intro y hy
      exact dvd_iff_isRoot.mpr (mem_fixed.mp hy).2
  obtain ⟨q,hq⟩ := hd
  have hn : q ≠ 0 := fun h => hp (by rwa [h,mul_zero] at hq)
  refine ⟨q,by rwa [map_nodal],hn,?_,?_⟩
  · change A.card + q.natDegree = p.natDegree
    rw [hq,natDegree_mul Lagrange.nodal_ne_zero hn,Lagrange.natDegree_nodal]
  · intro y hy hfix hzero
    apply hfix
    apply mem_fixed.mpr
    refine ⟨hy,?_⟩
    rw [hq,eval_mul,hzero,mul_zero]

/-- Multiply the polynomial supplied to the functional by a fixed factor. -/
noncomputable def trim (L : K[X][X] →ₗ[K[X]] K[X]) (G : K[X]) :
    K[X][X] →ₗ[K[X]] K[X] := L.comp (LinearMap.mulLeft K[X] (G.map C))

theorem trim_apolar_iff (L : K[X][X] →ₗ[K[X]] K[X]) (G : K[X]) (q : K[X][X]) (b : ℕ) :
    ApolarThrough (trim L G) q b ↔ ApolarThrough L (G.map C*q) b := by
  simp only [ApolarThrough,trim,LinearMap.comp_apply,LinearMap.mulLeft_apply,mul_assoc]

/-- The trimmed pencil still has affine moments through the adjusted degree. -/
theorem trim_affine (m : ℕ → K[X]) {d : ℕ} (hm : ∀ j ≤ d, (m j).natDegree ≤ 1)
    (G : K[X]) (j : ℕ) (hj : G.natDegree+j ≤ d) :
    ((trim (functional m) G) (X^j)).natDegree ≤ 1 := by
  have hd : (G*X^j).natDegree ≤ d := by
    exact (natDegree_mul_le.trans (Nat.add_le_add_left (natDegree_X_pow_le j) _)).trans hj
  simpa only [trim,LinearMap.comp_apply,LinearMap.mulLeft_apply,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_X] using functional_const_degree m hm (G*X^j) hd

/-- Multiplication by a nonzero fixed factor injects all lower-degree kernels
of the trimmed pencil into the preceding catalecticant of the original. -/
theorem trim_minimal (L : K[X][X] →ₗ[K[X]] K[X]) (G : K[X]) (hG : G ≠ 0)
    {r b : ℕ} (hprev : ∀ p : K[X][X], p.natDegree ≤ G.natDegree+r → ApolarThrough L p b → p=0) :
    ∀ q : K[X][X], q.natDegree ≤ r → ApolarThrough (trim L G) q b → q=0 := by
  intro q hq ha
  have hg : G.map (C : K →+* K[X]) ≠ 0 := (Polynomial.map_ne_zero_iff C_injective).mpr hG
  have hd : (G.map C*q).natDegree ≤ G.natDegree+r :=
    natDegree_mul_le.trans (Nat.add_le_add (natDegree_map_le) hq)
  exact (mul_eq_zero.mp (hprev _ hd ((trim_apolar_iff L G q b).mp ha))).resolve_left hg

/-- Multiplying a sparse atomic functional by a fixed-site vanisher removes exactly
the contributions at those sites, leaving a valid representation on the complement. -/
theorem weighted_nodal [DecidableEq K] (E A : Finset K) (w : K → K) (p : K[X]) :
    weighted E (RingHom.id K) w (Lagrange.nodal A id*p) =
      weighted (E \ A) (RingHom.id K) (fun y => w y*(Lagrange.nodal A id).eval y) p := by
  classical
  simp only [weighted_apply,RingHom.id_apply,eval_mul]
  rw [←sum_sdiff (s₁ := E ∩ A) (s₂ := E) inter_subset_left]
  have hz : ∑ y ∈ E ∩ A, w y * ((Lagrange.nodal A id).eval y * p.eval y) = 0 := by
    apply sum_eq_zero
    intro y hy
    rw [show (Lagrange.nodal A id).eval y=0 from Lagrange.eval_nodal_at_node (v:=id) (mem_inter.mp hy).2,
      zero_mul,mul_zero]
  rw [hz,add_zero]
  congr 1
  · ext y; simp
  · funext y; ring

/-- Remove a fixed factor of coordinate degree c. If the quotient has degree
at most r+1 and the original locator was minimal in degree c+r+1, its full
chart evaluation satisfies the strengthened parameter-degree bound. -/
theorem trimmed_chart_degree (m : ℕ → K[X]) (G : K[X]) (hg : G ≠ 0) (q : K[X][X])
    {d r : ℕ} (hr : r+1 ≤ d) (hl : 2*r ≤ d) (hq : q.natDegree ≤ r+1)
    (hm : ∀ j ≤ G.natDegree+d, (m j).natDegree ≤ 1)
    (ha : ApolarThrough (functional m) (G.map C*q) (d-(r+1)))
    (hi : ∀ p : K[X][X], p.natDegree ≤ G.natDegree+r →
      ApolarThrough (functional m) p (d-r) → p=0)
    (x z : K) (hxz : x ≠ z) (hz : G.eval z ≠ 0)
    (hc : IsCoprime ((G.map C*q).eval (C x)) ((G.map C*q).eval (C z))) :
    (d-2*r)*((G.map C*q).eval (C z)).natDegree ≤ r+1 := by
  classical
  let L := trim (functional m) G
  let μ (j : ℕ) := L (X^j)
  have hμ : functional μ = L := functional_moments _
  let b (i : Fin ((r+1)+1)) := q.coeff i.val
  have hb : form b=q := form_coeff q hq
  have he (y : K) : (family b).map (evalRingHom y)=q.eval (C y) := by rw [←eval_form, hb]
  have hca : IsCoprime ((family b).map (evalRingHom x)) ((family b).map (evalRingHom z)) := by
    rw [he,he]
    rw [eval_mul,eval_mul] at hc
    exact IsCoprime.mono (dvd_mul_left _ _) (dvd_mul_left _ _) hc
  have hker : catalecticant μ d (r+1) *ᵥ b=0 := by
    have happ := (trim_apolar_iff (functional m) G q _).mpr ha
    have hs := (equations_iff_apolar μ b).mpr (by rwa [hμ,hb])
    exact funext fun j => hs j.val (by have := j.isLt; omega)
  have hmin (v : Fin (r+1) → K[X]) (hv : catalecticant μ d r *ᵥ v=0) : v=0 := by
    have happ : ApolarThrough (functional μ) (form v) (d-r) := by
      apply (equations_iff_apolar μ v).mp
      intro j hj
      exact congrFun hv ⟨j,by omega⟩
    rw [hμ] at happ
    have hform := trim_minimal (functional m) G hg hi _ (form_degree _) happ
    funext i
    simpa only [coeff_form,coeff_zero,Pi.zero_apply] using congrArg (fun p : K[X][X] => p.coeff i.val) hform
  have hh := chart_evaluation_degree μ hr hl (fun j hj => trim_affine m hm G j (by omega))
    b hker hmin x z hxz hca
  rw [he] at hh
  rwa [eval_mul,eval_map_apply,natDegree_C_mul hz]

#print axioms trimmed_chart_degree
#print axioms split_fixed
#print axioms trim_minimal
#print axioms weighted_nodal

end ProximityGap.ApolarFixedFactors
