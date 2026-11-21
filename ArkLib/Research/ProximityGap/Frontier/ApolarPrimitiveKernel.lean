/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarPencilExtraction
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Polynomial.Content

/-! # Primitive polynomial vectors in a catalecticant kernel -/

open Polynomial Finset Matrix
namespace ProximityGap.ApolarPrimitiveKernel

variable {K : Type*} [Field K]

/-- Package the locator coefficients into a bivariate polynomial, with parameter
as the outer variable and the evaluation coordinate as the inner variable. -/
noncomputable def family {n : ℕ} (w : Fin n → K[X]) : K[X][X] :=
  ∑ i, (w i).map (C : K →+* K[X]) * C (X^i.val)

/-- Specializing the parameter specializes each coordinate coefficient. -/
theorem coeff_family {n : ℕ} (w : Fin n → K[X]) (t : K) (j : Fin n) :
    ((family w).eval (C t)).coeff j.val = (w j).eval t := by
  classical
  simp only [family,eval_finsetSum,eval_mul,eval_C,eval_map,eval₂_hom,finsetSum_coeff,
    coeff_C_mul_X_pow]
  rw [sum_eq_single j]
  · simp
  · intro i hi hn
    simp [Ne.symm (show i.val ≠ j.val from fun h => hn (Fin.ext h))]
  · simp

/-- A nonzero solution to homogeneous polynomial equations can be chosen primitive.
Its binary-coordinate form remains nonzero at every affine parameter. -/
theorem primitive_kernel {m : Type*} {n : ℕ} (A : Matrix m (Fin (n+1)) K[X])
    (v : Fin (n+1) → K[X]) (hv : v ≠ 0) (hker : A *ᵥ v = 0) :
    ∃ w : Fin (n+1) → K[X], w ≠ 0 ∧ A *ᵥ w = 0 ∧
      (∀ t : K, (family w).eval (C t) ≠ 0) ∧
      ∃ g : K[X], g ≠ 0 ∧ ∀ i, v i = g * w i := by
  classical
  let _ : NormalizedGCDMonoid K[X] := Classical.arbitrary _
  obtain ⟨w, hw, hgcd⟩ := Finset.extract_gcd (s := univ) v univ_nonempty
  have he (i) := hw i (mem_univ _)
  have hg : univ.gcd v ≠ 0 := by
    intro h
    exact hv (funext fun i => (Finset.gcd_eq_zero_iff.mp h) i (mem_univ _))
  have hvs : v = (univ.gcd v) • w := by funext i; exact he i
  have hn : w ≠ 0 := fun h => hv (by rw [hvs,h,smul_zero])
  have hwker : A *ᵥ w = 0 := by
    rw [hvs,Matrix.mulVec_smul] at hker
    exact (smul_eq_zero.mp hker).resolve_left hg
  refine ⟨w,hn,hwker,?_,univ.gcd v,hg,he⟩
  intro t hzero
  have hdiv : X-C t ∣ univ.gcd w := by
    apply Finset.dvd_gcd
    intro i _
    apply dvd_iff_isRoot.mpr
    change (w i).eval t = 0
    rw [← coeff_family w t i, hzero, coeff_zero]
  rw [hgcd] at hdiv
  obtain ⟨a,ha⟩ := hdiv
  have hh := congrArg (eval t) ha
  simp at hh

/-- The primitive solution can be sampled at two distinct coordinate points,
with coprime parameter polynomials and no loss of the family's parameter degree. -/
theorem primitive_kernel_chart [IsAlgClosed K] [Infinite K] {m : Type*} {n : ℕ}
    (A : Matrix m (Fin (n+1)) K[X]) (v : Fin (n+1) → K[X]) (hv : v ≠ 0)
    (hker : A *ᵥ v = 0) (avoid : Finset K) :
    ∃ w : Fin (n+1) → K[X], w ≠ 0 ∧ A *ᵥ w = 0 ∧
      (∀ t : K, (family w).eval (C t) ≠ 0) ∧
      ∃ x ∉ avoid, ∃ y ∉ avoid, x ≠ y ∧
        ((family w).map (evalRingHom x)).natDegree = (family w).natDegree ∧
        ((family w).map (evalRingHom y)).natDegree = (family w).natDegree ∧
        IsCoprime ((family w).map (evalRingHom x)) ((family w).map (evalRingHom y)) := by
  obtain ⟨w,hw,hker',hs,_⟩ := primitive_kernel A v hv hker
  exact ⟨w,hw,hker',hs,ApolarHankelMinors.exists_coprime_chart (family w) avoid hs⟩

/-- A polynomial kernel from the original finite alphabet gives a primitive family
over an algebraically closed extension, where all of its geometric parameter
fibers are nonzero and one can choose a chart disjoint from a finite set. -/
theorem primitive_kernel_extension_chart {L : Type*} [Field L] [IsAlgClosed L] [Infinite L]
    (φ : K →+* L) {m : Type*} {n : ℕ} (A : Matrix m (Fin (n+1)) K[X])
    (v : Fin (n+1) → K[X]) (hv : v ≠ 0) (hker : A *ᵥ v = 0) (avoid : Finset L) :
    ∃ w : Fin (n+1) → L[X], w ≠ 0 ∧ (A.map (Polynomial.map φ)) *ᵥ w = 0 ∧
      (∀ t : L, (family w).eval (C t) ≠ 0) ∧
      ∃ x ∉ avoid, ∃ y ∉ avoid, x ≠ y ∧
        ((family w).map (evalRingHom x)).natDegree = (family w).natDegree ∧
        ((family w).map (evalRingHom y)).natDegree = (family w).natDegree ∧
        IsCoprime ((family w).map (evalRingHom x)) ((family w).map (evalRingHom y)) := by
  let w (i : Fin (n+1)) := (v i).map φ
  have hw : w ≠ 0 := by
    intro he
    apply hv
    funext i
    exact (Polynomial.map_eq_zero_iff φ.injective).mp (congrFun he i)
  have hA : (A.map (Polynomial.map φ)) *ᵥ w = 0 := by
    funext j
    have hh := congrArg (Polynomial.map φ) (congrFun hker j)
    simpa only [Matrix.mulVec, dotProduct, Polynomial.map_sum, Polynomial.map_mul, Pi.zero_apply,
      Polynomial.map_zero, Matrix.map_apply, w] using hh
  exact primitive_kernel_chart _ w hw hA avoid

/-- The rectangular catalecticant at coordinate degree s. -/
def catalecticant (m : ℕ → K[X]) (d s : ℕ) :
    Matrix (Fin (d-s+1)) (Fin (s+1)) K[X] := fun j i => m (j.val+i.val)

/-- Starting with the kernel supplied by the bad parameters, select its least
coordinate degree over the algebraically closed alphabet extension and retain
both its primitive locator and injectivity at all smaller degrees. -/
theorem minimal_primitive_chart {L : Type*} [Field L] [IsAlgClosed L] [Infinite L]
    (φ : K →+* L) (m : ℕ → K[X]) {d e : ℕ}
    (hasKernel : ∃ v : Fin (e+1) → K[X], v ≠ 0 ∧ catalecticant m d e *ᵥ v = 0)
    (avoid : Finset L) :
    let μ := fun i => (m i).map φ
    ∃ s ≤ e, (∀ q < s, ∀ p : Fin (q+1) → L[X], catalecticant μ d q *ᵥ p = 0 → p = 0) ∧
      ∃ w : Fin (s+1) → L[X], w ≠ 0 ∧ catalecticant μ d s *ᵥ w = 0 ∧
        (∀ t : L, (family w).eval (C t) ≠ 0) ∧
        ∃ x ∉ avoid, ∃ y ∉ avoid, x ≠ y ∧
          ((family w).map (evalRingHom x)).natDegree = (family w).natDegree ∧
          ((family w).map (evalRingHom y)).natDegree = (family w).natDegree ∧
          IsCoprime ((family w).map (evalRingHom x)) ((family w).map (evalRingHom y)) := by
  classical
  let μ (i : ℕ) := (m i).map φ
  let P (s : ℕ) := ∃ w : Fin (s+1) → L[X], w ≠ 0 ∧ catalecticant μ d s *ᵥ w = 0
  obtain ⟨v,hv,hk⟩ := hasKernel
  obtain ⟨b,hb,hbker,_⟩ := primitive_kernel_extension_chart φ _ v hv hk avoid
  have hE : P e := ⟨b,hb,hbker⟩
  have hex : ∃ j, P j := ⟨e,hE⟩
  let s := Nat.find hex
  have hmin (q : ℕ) (h : q < s) (p : Fin (q+1) → L[X]) (hk : catalecticant μ d q *ᵥ p = 0) : p = 0 := by
    by_contra hn
    exact (Nat.find_min hex h) ⟨p,hn,hk⟩
  obtain ⟨p,hp,hpk⟩ := Nat.find_spec hex
  obtain ⟨w, hw, hkw, hfw, hchart⟩ := primitive_kernel_chart _ p hp hpk avoid
  exact ⟨s, Nat.find_min' hex hE, hmin, w, hw, hkw, hfw, hchart⟩

open Code
open scoped NNReal

/-- A family of actual bad scalars gives a least primitive apolar form on the
geometric parameter line, with no identically zero fiber and with a coprime
full-degree coordinate chart disjoint from any prescribed finite set. -/
theorem minimal_chart_of_mca_events {F L ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Field L] [IsAlgClosed L] [Infinite L] [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (φ : F →+* L) (dom : ι ↪ F) {k e d : ℕ} {δ : ℝ≥0}
    (u : WordStack F (Fin 2) ι) (bad : Finset F) (hs : e+1 < bad.card)
    (hed : e ≤ d) (hk : 1 ≤ k) (hd : k+d < Fintype.card ι)
    (he : Fintype.card ι - e ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊)
    (hbad : ∀ t ∈ bad, mcaEvent (ReedSolomon.code dom k : Set (ι → F)) δ (u 0) (u 1) t)
    (avoid : Finset L) :
    let H := (univ : Finset ι).map dom
    let μ := fun j => (ApolarHankelMinors.moment H (ApolarMcaSyndrome.coordinateRow dom (u 0))
      (ApolarMcaSyndrome.coordinateRow dom (u 1)) j).map φ
    ∃ s ≤ e, (∀ q < s, ∀ p : Fin (q+1) → L[X], catalecticant μ d q *ᵥ p = 0 → p = 0) ∧
      ∃ w : Fin (s+1) → L[X], w ≠ 0 ∧ catalecticant μ d s *ᵥ w = 0 ∧
        (∀ t : L, (family w).eval (C t) ≠ 0) ∧
        ∃ x ∉ avoid, ∃ y ∉ avoid, x ≠ y ∧
          ((family w).map (evalRingHom x)).natDegree = (family w).natDegree ∧
          ((family w).map (evalRingHom y)).natDegree = (family w).natDegree ∧
          IsCoprime ((family w).map (evalRingHom x)) ((family w).map (evalRingHom y)) := by
  obtain ⟨c,hc,hrec⟩ :=
    ArkLib.ProximityGap.Frontier.ApolarPencilExtraction.generic_locator_of_mca_events
      dom u bad hs hed hk hd he hbad
  apply minimal_primitive_chart φ _ (d := d) (e := e) _ avoid
  exact ⟨c,hc,funext fun j => hrec j.val j.isLt⟩

#print axioms minimal_chart_of_mca_events
#print axioms minimal_primitive_chart
#print axioms primitive_kernel_extension_chart
#print axioms primitive_kernel_chart

end ProximityGap.ApolarPrimitiveKernel
