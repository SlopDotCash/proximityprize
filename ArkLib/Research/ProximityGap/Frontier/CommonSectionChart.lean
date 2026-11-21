/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Finset.Preimage

/-! # One coordinate chart for a finite family of simple sections

Send an old coordinate `r` to infinity by setting `X = r + 1/U`. For a
polynomial bounded by weight `w`, the cleared polynomial has top coefficient
equal to its old value at `r`. One such chart works for all simple sections
and all evaluation sites simultaneously. -/

open Polynomial

namespace ProximityGap.CommonSectionChart

variable {K : Type*} [Field K]

/-- Homogenize to weight `w` after the coordinate change `X = r + 1/U`. -/
noncomputable def change (r : K) (w : ℕ) (p : K[X]) : K[X] :=
  reflect w (taylor r p)

theorem degree_le (r : K) (w : ℕ) (p : K[X]) (hp : p.natDegree ≤ w) :
    (change r w p).natDegree ≤ w :=
  natDegree_reflect_le.trans (max_le le_rfl (by simpa using hp))

@[simp] theorem top_coeff (r : K) (w : ℕ) (p : K[X]) :
    (change r w p).coeff w = p.eval r := by
  simp [change, revAt_le]

theorem degree_eq (r : K) (w : ℕ) (p : K[X]) (hp : p.natDegree ≤ w)
    (hr : p.eval r ≠ 0) : (change r w p).natDegree = w :=
  le_antisymm (degree_le r w p hp) (le_natDegree_of_ne_zero (by simpa using hr))

/-- Clearing the degree weights preserves products, including products whose
actual degrees fall below their weights. -/
theorem change_mul (r : K) {a b : ℕ} (p q : K[X])
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    change r (a+b) (p*q) = change r a p * change r b q := by
  simp only [change, taylor_mul]
  exact reflect_mul _ _ (by simpa using hp) (by simpa using hq)

/-- At a finite old site the polynomial value scales by the coordinate power. -/
theorem eval_site (r x : K) (w : ℕ) (p : K[X]) (hp : p.natDegree ≤ w) (hx : x ≠ r) :
    (change r w p).eval (x-r)⁻¹ = (x-r)⁻¹ ^ w * p.eval x := by
  have hn := sub_ne_zero.mpr hx
  let _ := invertibleOfNonzero hn
  have h := eval₂_reflect_mul_pow (RingHom.id K) (x-r) w (taylor r p) (by simpa using hp)
  simp only [eval₂_id, invOf_eq_inv, taylor_apply, eval_comp, eval_add, eval_X, eval_C,
    sub_add_cancel] at h
  change (reflect w (p.comp (X+C r))).eval (x-r)⁻¹ = _
  rw [← h, inv_pow]
  field_simp

/-- Multiplying the received affine line by the same power preserves the
agreement set of each transformed section. -/
theorem eval_site_eq_iff (r x : K) (d : ℕ) (q : K[X]) (hq : q.natDegree ≤ d)
    (hx : x ≠ r) (lineValue : K) :
    (change r d q).eval (x-r)⁻¹ = (x-r)⁻¹ ^ d * lineValue ↔ q.eval x = lineValue := by
  rw [eval_site r x d q hq hx, mul_right_inj' (pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr hx)))]

/-- All selected residual derivatives attain their prescribed degree after one
change of chart. Any additional nonzero coordinate tests can be included
among the polynomials. The map on the original sites is injective. -/
theorem simultaneous [Infinite K] {ι : Type*} (labels : Finset ι) (sites : Finset K)
    (p : ι → K[X]) (w : ι → ℕ) (hp : ∀ i ∈ labels, p i ≠ 0)
    (hw : ∀ i ∈ labels, (p i).natDegree ≤ w i) :
    ∃ r : K, r ∉ sites ∧ Function.Injective (fun x : K => (x-r)⁻¹) ∧
      ∀ i ∈ labels, (p i).eval r ≠ 0 ∧ (change r (w i) (p i)).natDegree = w i := by
  classical
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset (sites ∪ labels.biUnion (fun i => (p i).roots.toFinset))
  have h := Finset.notMem_union.mp hr
  refine ⟨r, h.1, (inv_injective.comp sub_left_injective), ?_⟩
  intro i hi
  have hv : (p i).eval r ≠ 0 := by
    intro hz
    exact h.2 (Finset.mem_biUnion.mpr ⟨i, hi, Multiset.mem_toFinset.mpr ((mem_roots (hp i hi)).mpr hz)⟩)
  exact ⟨hv, degree_eq _ _ _ (hw i hi) hv⟩

private theorem horner_degree (a b q : K[X]) {v d : ℕ} (ha : a.natDegree ≤ v+d)
    (hb : b.natDegree ≤ v) (hq : q.natDegree ≤ d) : (a+b*q).natDegree ≤ v+d :=
  natDegree_add_le_of_degree_le ha (natDegree_mul_le.trans (Nat.add_le_add hb hq))

private theorem horner_chart (r : K) (a b q : K[X]) {v d : ℕ}
    (hb : b.natDegree ≤ v) (hq : q.natDegree ≤ d) :
    change r (v+d) (a+b*q) = change r (v+d) a + change r v b * change r d q := by
  have add (f g : K[X]) : change r (v+d) (f+g) = change r (v+d) f + change r (v+d) g := by
    simp only [change, map_add, reflect_add]
  rw [add, change_mul r b q hb hq]

private theorem change_C_mul (r c : K) (w : ℕ) (p : K[X]) :
    change r w (C c * p) = C c * change r w p := by
  simp only [change, taylor_mul, taylor_C, reflect_C_mul]

/-- The cubic evaluated on a section, in ascending order of coefficients. -/
noncomputable def cubic (a b c e q : K[X]) : K[X] := a + (b + (c + e*q)*q)*q

/-- Evaluation of the cubic's ordinate derivative on a section. -/
noncomputable def residual (b c e q : K[X]) : K[X] := b + (C (2:K)*c + (C (3:K)*e)*q)*q

/-- The section equation is covariant under the common chart, including
fibers where specialized coefficients or the section drop degree. -/
theorem cubic_chart (r : K) {v d : ℕ} (a b c e q : K[X])
    (hb : b.natDegree ≤ v+d+d) (hc : c.natDegree ≤ v+d)
    (he : e.natDegree ≤ v) (hq : q.natDegree ≤ d) :
    change r (v+d+d+d) (cubic a b c e q) = cubic (change r (v+d+d+d) a)
      (change r (v+d+d) b) (change r (v+d) c) (change r v e) (change r d q) := by
  unfold cubic
  have h₁ := horner_degree _ _ _ hc he hq
  have h₂ := horner_degree _ _ _ hb h₁ hq
  rw [horner_chart _ _ _ _ h₂ hq, horner_chart _ _ _ _ h₁ hq, horner_chart _ _ _ _ he hq]

private theorem residual_degree {v d : ℕ} (b c e q : K[X])
    (hb : b.natDegree ≤ v+d+d) (hc : c.natDegree ≤ v+d)
    (he : e.natDegree ≤ v) (hq : q.natDegree ≤ d) :
    (residual b c e q).natDegree ≤ v+d+d :=
  horner_degree _ _ _ hb (horner_degree _ _ _ ((natDegree_C_mul_le _ _).trans hc)
    ((natDegree_C_mul_le _ _).trans he) hq) hq

theorem residual_chart (r : K) {v d : ℕ} (b c e q : K[X])
    (hc : c.natDegree ≤ v+d) (he : e.natDegree ≤ v) (hq : q.natDegree ≤ d) :
    change r (v+d+d) (residual b c e q) = residual
      (change r (v+d+d) b) (change r (v+d) c) (change r v e) (change r d q) := by
  unfold residual
  have h₁ := horner_degree _ _ q ((natDegree_C_mul_le _ _).trans hc : (C (2:K)*c).natDegree ≤ _)
    ((natDegree_C_mul_le _ _).trans he : (C (3:K)*e).natDegree ≤ _) hq
  rw [horner_chart _ _ _ _ h₁ hq, horner_chart _ _ _ _ ((natDegree_C_mul_le _ _).trans he) hq,
    change_C_mul, change_C_mul]

/-- A single change puts every selected simple cubic section in full residual
degree `W-d`, preserves all its roots as a section, and keeps distinct sites
finite and distinct. Here `v = W-3d` is the weight of the leading coefficient. -/
theorem cubic_sections [Infinite K] {ι : Type*} (labels : Finset ι) (sites : Finset K)
    (a b c e q : ι → K[X]) (v d : ℕ)
    (hb : ∀ i ∈ labels, (b i).natDegree ≤ v+d+d) (hc : ∀ i ∈ labels, (c i).natDegree ≤ v+d)
    (he : ∀ i ∈ labels, (e i).natDegree ≤ v) (hq : ∀ i ∈ labels, (q i).natDegree ≤ d)
    (hroot : ∀ i ∈ labels, cubic (a i) (b i) (c i) (e i) (q i) = 0)
    (hsimple : ∀ i ∈ labels, residual (b i) (c i) (e i) (q i) ≠ 0) :
    ∃ r : K, r ∉ sites ∧ Function.Injective (fun x : K => (x-r)⁻¹) ∧ ∀ i ∈ labels,
      cubic (change r (v+d+d+d) (a i)) (change r (v+d+d) (b i))
        (change r (v+d) (c i)) (change r v (e i)) (change r d (q i)) = 0 ∧
      (residual (change r (v+d+d) (b i)) (change r (v+d) (c i)) (change r v (e i))
        (change r d (q i))).natDegree = v+d+d := by
  obtain ⟨r, hr, hinj, h⟩ := simultaneous labels sites _ (fun _ => v+d+d) hsimple
    (fun i hi => residual_degree _ _ _ _ (hb i hi) (hc i hi) (he i hi) (hq i hi))
  refine ⟨r, hr, hinj, fun i hi => ⟨?_, ?_⟩⟩
  · rw [← cubic_chart _ _ _ _ _ _ (hb i hi) (hc i hi) (he i hi) (hq i hi), hroot i hi]
    simp [change]
  · rw [← residual_chart _ _ _ _ _ (hc i hi) (he i hi) (hq i hi)]
    exact (h i hi).2

private theorem cubic_expansion (f : K[X][X]) (hf : f.natDegree ≤ 3) :
    f = C (f.coeff 0) + C (f.coeff 1)*X + C (f.coeff 2)*X^2 + C (f.coeff 3)*X^3 := by
  have h := f.as_sum_range_C_mul_X_pow' (n := 4) (by omega)
  simpa [Finset.sum_range_succ] using h

/-- The Horner expressions used in the chart are precisely ordinary evaluation
and derivative evaluation of the original bivariate factor. -/
theorem section_values (f : K[X][X]) (hf : f.natDegree ≤ 3) (q : K[X]) :
    f.eval q = cubic (f.coeff 0) (f.coeff 1) (f.coeff 2) (f.coeff 3) q ∧
    f.derivative.eval q = residual (f.coeff 1) (f.coeff 2) (f.coeff 3) q := by
  constructor
  · conv_lhs => rw [cubic_expansion f hf]
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, cubic]
    ring
  · conv_lhs => rw [cubic_expansion f hf]
    simp [residual, derivative_add, derivative_mul, derivative_pow, C_ofNat]
    ring

/-- The finitely many old base coordinates forbidden by nonzero tests over a
coefficient-field extension, for example the constant, leading, and
discriminant tests over the scalar function field. -/
noncomputable def forbidden {L : Type*} [Field L] (φ : K →+* L) (tests : Finset L[X]) :
    Finset K := by
  classical
  exact (tests.biUnion (fun p => p.roots.toFinset)).preimage φ φ.injective.injOn

theorem avoids_tests {L : Type*} [Field L] (φ : K →+* L) (tests : Finset L[X])
    (h : ∀ p ∈ tests, p ≠ 0) {r : K} (hr : r ∉ forbidden φ tests) :
    ∀ p ∈ tests, p.eval (φ r) ≠ 0 := by
  classical
  intro p hp he
  exact hr (Finset.mem_preimage.mpr (Finset.mem_biUnion.mpr
    ⟨p, hp, Multiset.mem_toFinset.mpr ((mem_roots (h p hp)).mpr he)⟩))

/-- For genuine specialized bivariate cubics one chart preserves every section
and puts the ordinate derivative in its exact prescribed degree. -/
theorem simple_fibers [Infinite K] {ι : Type*} (labels : Finset ι) (sites : Finset K)
    {L : Type*} [Field L] (φ : K →+* L) (tests : Finset L[X]) (ht : ∀ p ∈ tests, p ≠ 0)
    (f : ι → K[X][X]) (q : ι → K[X]) (v d : ℕ)
    (hf : ∀ i ∈ labels, (f i).natDegree ≤ 3)
    (hb : ∀ i ∈ labels, ((f i).coeff 1).natDegree ≤ v+d+d)
    (hc : ∀ i ∈ labels, ((f i).coeff 2).natDegree ≤ v+d)
    (he : ∀ i ∈ labels, ((f i).coeff 3).natDegree ≤ v)
    (hq : ∀ i ∈ labels, (q i).natDegree ≤ d)
    (hroot : ∀ i ∈ labels, (f i).eval (q i) = 0)
    (hsimple : ∀ i ∈ labels, (f i).derivative.eval (q i) ≠ 0) :
    ∃ r : K, r ∉ sites ∧ (∀ p ∈ tests, p.eval (φ r) ≠ 0) ∧ Function.Injective (fun x : K => (x-r)⁻¹) ∧ ∀ i ∈ labels,
      cubic (change r (v+d+d+d) ((f i).coeff 0)) (change r (v+d+d) ((f i).coeff 1))
        (change r (v+d) ((f i).coeff 2)) (change r v ((f i).coeff 3)) (change r d (q i)) = 0 ∧
      (residual (change r (v+d+d) ((f i).coeff 1)) (change r (v+d) ((f i).coeff 2))
        (change r v ((f i).coeff 3)) (change r d (q i))).natDegree = v+d+d := by
  classical
  obtain ⟨r, hr, hinj, h⟩ := cubic_sections labels (sites ∪ forbidden φ tests)
    _ _ _ _ _ v d hb hc he hq
    (fun i hi => (section_values _ (hf i hi) _).1.symm.trans (hroot i hi))
    (fun i hi => (section_values _ (hf i hi) _).2 ▸ hsimple i hi)
  have hs := Finset.notMem_union.mp hr
  exact ⟨r, hs.1, avoids_tests φ tests ht hs.2, hinj, h⟩

#print axioms simple_fibers
#print axioms cubic_sections
#print axioms eval_site_eq_iff

end ProximityGap.CommonSectionChart
