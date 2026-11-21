/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCoordinateWeight
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeActualPopulations
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Derivative
import ArkLib.Data.Polynomial.Bivariate
import Mathlib.Tactic

/-! # A common coordinate chart for finitely many simple polynomial sections

At a fixed weight D the change of coordinate x ↦ r + 1/x acts on a polynomial p by
x^D p(r + 1/x). Its top coefficient equals p(r).
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeMobiusSections

open Finset Polynomial
open scoped Polynomial

variable {K : Type*} [Field K]

/-- Graded change of coordinate defined by Taylor translation followed by reflection. -/
noncomputable def chart (r : K) (D : ℕ) : K[X] →+ K[X] where
  toFun p := (p.taylor r).reflect D
  map_zero' := by simp
  map_add' p q := by simp

theorem chart_degree_le (r : K) (D : ℕ) (p : K[X]) (hp : p.natDegree ≤ D) :
    (chart r D p).natDegree ≤ D := by
  exact natDegree_reflect_le.trans (max_le le_rfl ((natDegree_taylor _ _).le.trans hp))

theorem chart_top (r : K) (D : ℕ) (p : K[X]) : (chart r D p).coeff D = p.eval r := by
  simp [chart, taylor_coeff_zero]

theorem chart_degree (r : K) (D : ℕ) (p : K[X]) (hp : p.natDegree ≤ D) (hr : p.eval r ≠ 0) :
    (chart r D p).natDegree = D :=
  (chart_degree_le r D p hp).antisymm (le_natDegree_of_ne_zero ((chart_top r D p).symm ▸ hr))

theorem chart_mul (r : K) (A B : ℕ) (p q : K[X]) (hp : p.natDegree ≤ A) (hq : q.natDegree ≤ B) :
    chart r (A + B) (p * q) = chart r A p * chart r B q := by
  change ((p * q).taylor r).reflect (A + B) = _
  rw [taylor_mul, reflect_mul _ _ ((natDegree_taylor _ _).le.trans hp)
    ((natDegree_taylor _ _).le.trans hq)]
  rfl

theorem chart_pow (r : K) (d j : ℕ) (q : K[X]) (hq : q.natDegree ≤ d) :
    chart r (j * d) (q ^ j) = chart r d q ^ j := by
  induction j with
  | zero => simp [chart, reflect_one]
  | succ j ih =>
    rw [pow_succ, Nat.succ_mul, chart_mul, ih, pow_succ]
    · exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ hq)
    · exact hq

/-- Transform each coefficient using its residual coordinate weight W−jd. -/
noncomputable def plane (r : K) (W d : ℕ) (F : K[X][X]) : K[X][X] :=
  ∑ j ∈ F.support, monomial j (chart r (W - j * d) (F.coeff j))

theorem plane_coeff (r : K) (W d : ℕ) (F : K[X][X]) (j : ℕ) :
    (plane r W d F).coeff j = chart r (W - j * d) (F.coeff j) := by
  classical
  by_cases hj : j ∈ F.support
  · simp [plane, finsetSum_coeff, coeff_monomial, hj]
  · simp [plane, finsetSum_coeff, coeff_monomial, hj, notMem_support_iff.mp hj]

/-- Weighted substitution commutes with the coordinate change on the actual polynomial graph. -/
theorem plane_graph (r : K) (W d : ℕ) (F : K[X][X]) (q : K[X]) (hq : q.natDegree ≤ d)
    (hw : ∀ j ∈ F.support, (F.coeff j).natDegree + j * d ≤ W) :
    (plane r W d F).eval (chart r d q) = chart r W (F.eval q) := by
  classical
  rw [plane, eval_finsetSum, eval_eq_sum, sum_def, map_sum]
  apply sum_congr rfl
  intro j hj
  rw [eval_monomial]
  have h := hw j hj
  have he : W = (W - j * d) + j * d := by omega
  conv_rhs => arg 1; rw [he]
  rw [chart_mul _ _ _ _ _ (by omega) (natDegree_pow_le.trans (Nat.mul_le_mul_left _ hq)),
    chart_pow _ _ _ _ hq]

private theorem chart_C_mul (r : K) (D : ℕ) (a : K) (p : K[X]) :
    chart r D (C a * p) = C a * chart r D p := by
  change ((C a * p).taylor r).reflect D = _
  rw [taylor_mul, taylor_C, reflect_C_mul]
  rfl

theorem plane_derivative (r : K) (W d : ℕ) (F : K[X][X]) :
    (plane r W d F).derivative = plane r (W - d) d F.derivative := by
  ext1 j
  rw [coeff_derivative, plane_coeff, plane_coeff, coeff_derivative]
  rw [show (↑j + 1 : K[X]) = C ((j : K) + 1) from by simp]
  rw [mul_comm (F.coeff (j + 1)), chart_C_mul, mul_comm _ (C _)]
  congr 2
  rw [Nat.succ_mul, Nat.sub_sub, add_comm]

private theorem eval_degree (W d : ℕ) (F : K[X][X]) (q : K[X]) (hq : q.natDegree ≤ d)
    (hw : ∀ j ∈ F.support, (F.coeff j).natDegree + j * d ≤ W) :
    (F.eval q).natDegree ≤ W := by
  rw [eval_eq_sum, sum_def]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact natDegree_mul_le.trans ((Nat.add_le_add_left
    (natDegree_pow_le.trans (Nat.mul_le_mul_left j hq)) _).trans (hw j hj))

private theorem derivative_weight (W d : ℕ) (F : K[X][X])
    (hw : ∀ j ∈ F.support, (F.coeff j).natDegree + j * d ≤ W) :
    ∀ j ∈ F.derivative.support, (F.derivative.coeff j).natDegree + j * d ≤ W - d := by
  intro j hj
  have hne : F.coeff (j + 1) ≠ 0 := by
    intro he
    exact (mem_support_iff.mp hj) (by rw [coeff_derivative, he, zero_mul])
  have h := hw (j + 1) (mem_support_iff.mpr hne)
  rw [Nat.succ_mul] at h
  rw [coeff_derivative, show (↑j + 1 : K[X]) = C ((j : K) + 1) from by simp, mul_comm]
  have := natDegree_C_mul_le ((j : K) + 1) (F.coeff (j + 1))
  omega

/-- A simple-section derivative avoiding the chart center attains exactly W−d in the new chart. -/
theorem derivative_graph_degree (r : K) (W d : ℕ) (F : K[X][X]) (q : K[X])
    (hq : q.natDegree ≤ d)
    (hw : ∀ j ∈ F.support, (F.coeff j).natDegree + j * d ≤ W)
    (hr : (F.derivative.eval q).eval r ≠ 0) :
    ((plane r W d F).derivative.eval (chart r d q)).natDegree = W - d := by
  have h := derivative_weight W d F hw
  rw [plane_derivative, plane_graph _ _ _ _ _ hq h,
    chart_degree _ _ _ (eval_degree _ _ _ _ hq h) hr]

/-- The received symbols at the new coordinate are scaled by precisely the same
factor as each degree-d selected polynomial. -/
theorem chart_eval (r a : K) (ha : a ≠ r) (d : ℕ) (p : K[X]) (hd : p.natDegree ≤ d) :
    (chart r d p).eval ((a - r)⁻¹) = ((a - r)⁻¹) ^ d * p.eval a := by
  have hn := sub_ne_zero.mpr ha
  let _ : Invertible (a - r) := invertibleOfNonzero hn
  have hh := eval₂_reflect_mul_pow (RingHom.id K) (a - r) d (p.taylor r)
    ((natDegree_taylor _ _).le.trans hd)
  simp only [invOf_eq_inv, eval₂_id, taylor_eval, sub_add_cancel] at hh
  change ((p.taylor r).reflect d).eval _ = _
  rw [← hh]
  rw [← mul_assoc, mul_comm ((a - r)⁻¹ ^ d) _, mul_assoc, ← mul_pow, inv_mul_cancel₀ hn,
    one_pow, mul_one]

private theorem fiber_swap (p : K[X][X]) (z : K) :
    (Bivariate.swap p).map (evalRingHom z) = p.eval (C z) := by
  simpa only [Bivariate.evalY, Bivariate.evalX_eq_map] using
    (Bivariate.evalY_eq_evalX_swap z p).symm

/-- Reparameterize one scalar polynomial coefficient along its coordinate axis. -/
private noncomputable def along (r : K) (D : ℕ) (p : K[X][X]) : K[X][X] :=
  ∑ i ∈ p.support, monomial i (chart r D (p.coeff i))

private theorem along_coeff (r : K) (D : ℕ) (p : K[X][X]) (i : ℕ) :
    (along r D p).coeff i = chart r D (p.coeff i) := by
  classical
  by_cases hi : i ∈ p.support
  · simp [along, finsetSum_coeff, coeff_monomial, hi]
  · simp [along, finsetSum_coeff, coeff_monomial, hi, notMem_support_iff.mp hi]

private theorem along_eval (r z : K) (D : ℕ) (p : K[X][X]) :
    (along r D p).eval (C z) = chart r D (p.eval (C z)) := by
  classical
  rw [along, eval_finsetSum, eval_eq_sum, sum_def, map_sum]
  apply sum_congr rfl
  intro i _
  rw [eval_monomial, ← C_pow, mul_comm (p.coeff i), chart_C_mul, mul_comm]

/-- A single trivariate polynomial works on all transformed scalar fibers. -/
noncomputable def surfaceChart (r : K) (W d : ℕ) (f : K[X][X][X]) : K[X][X][X] :=
  ∑ j ∈ f.support, monomial j (along r (W - j * d) (f.coeff j))

private theorem chart_ne_zero (r : K) (D : ℕ) {p : K[X]} (hp : p ≠ 0) : chart r D p ≠ 0 := by
  change (p.taylor r).reflect D ≠ 0
  exact fun h => hp ((taylorEquiv r).injective (by simpa using reflect_eq_zero_iff.mp h))

theorem surface_coeff (r : K) (W d : ℕ) (f : K[X][X][X]) (j i : ℕ) :
    ((surfaceChart r W d f).coeff j).coeff i = chart r (W - j * d) ((f.coeff j).coeff i) := by
  classical
  by_cases hj : j ∈ f.support
  · simp [surfaceChart, finsetSum_coeff, coeff_monomial, hj, along_coeff]
  · simp [surfaceChart, finsetSum_coeff, coeff_monomial, hj, notMem_support_iff.mp hj]

/-- The coordinate reparameterization preserves the entire scalar/value support. -/
theorem scalar_value_support (r : K) (W d : ℕ) (f : K[X][X][X]) (j i : ℕ) :
    ((surfaceChart r W d f).coeff j).coeff i ≠ 0 ↔ (f.coeff j).coeff i ≠ 0 := by
  rw [surface_coeff]
  exact ⟨fun hn he => hn (by rw [he, map_zero]), chart_ne_zero _ _⟩

theorem surface_fiber (r z : K) (W d : ℕ) (f : K[X][X][X]) :
    (surfaceChart r W d f).map (evalRingHom (C z)) =
      plane r W d (f.map (evalRingHom (C z))) := by
  classical
  ext1 j
  rw [coeff_map, plane_coeff, coeff_map]
  change ((surfaceChart r W d f).coeff j).eval (C z) = chart r _ ((f.coeff j).eval (C z))
  by_cases hj : j ∈ f.support
  · simp [surfaceChart, finsetSum_coeff, coeff_monomial, hj, along_eval]
  · simp [surfaceChart, finsetSum_coeff, coeff_monomial, hj, notMem_support_iff.mp hj]

/-- One center outside the original evaluation domain simultaneously attains top degree
for all the nonzero residual polynomials in a finite family. -/
theorem common_center [Infinite K] {L : Type*} (M : Finset L) (D : Finset K) (R : L → K[X])
    (hn : ∀ z ∈ M, R z ≠ 0) :
    ∃ r : K, r ∉ D ∧ ∀ z ∈ M, (R z).eval r ≠ 0 := by
  classical
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset (D ∪ M.biUnion fun z => (R z).roots.toFinset)
  refine ⟨r, fun h => hr (mem_union_left _ h), fun z hz h => hr (mem_union_right _ ?_)⟩
  exact mem_biUnion.mpr ⟨z, hz, Multiset.mem_toFinset.mpr ((mem_roots (hn z hz)).mpr h)⟩

private theorem section_weight {K : Type} [Field K] (d : ℕ) (f : K[X][X][X]) (z : K) (j : ℕ)
    (hj : j ∈ (f.map (evalRingHom (C z))).support) :
    ((f.map (evalRingHom (C z))).coeff j).natDegree + j * d ≤
      SecondPrimeCoordinateWeight.weight d f := by
  have hn : f.coeff j ≠ 0 := fun he => (mem_support_iff.mp hj) (by simp [coeff_map, he])
  obtain ⟨i, hi, he, _⟩ := Bivariate.exists_max_index_degreeX (f.coeff j) hn
  have hw := SecondPrimeCoordinateWeight.coeff_weight_le d f
    (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi))
  change ((f.coeff j).coeff i).natDegree + j * d ≤ _ at hw
  rw [he] at hw
  apply (Nat.add_le_add_right _ _).trans hw
  rw [coeff_map, coe_evalRingHom, ← fiber_swap, ← Bivariate.natDegreeY_swap]
  exact natDegree_map_le

open SecondPrimeActualPopulations
open scoped NNReal

variable {F I : Type} [Field F] [DecidableEq F] [Fintype I]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- One chart simultaneously preserves actual selected cubic sections, their received
agreements, and the exact degree of their specialized value derivatives. At most 161
labels are discarded in finding the simple sections. -/
theorem actual_cubic_chart {K : Type} [Field K] [Infinite K]
    (fam : Family dom δ u) (σ : F →+* K) (f Q : K[X][X][X])
    (hchar : (3 : K) ≠ 0) (hi : Irreducible f) (hb : f.natDegree = 3)
    (hQ : Q ≠ 0) (hdiv : f ∣ Q)
    (htri : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 34) :
    let d := 67108863
    let W := SecondPrimeCoordinateWeight.weight d f
    ∃ r : K, (∀ i, σ (dom i) ≠ r) ∧ ∃ S ⊆ population fam σ f,
      (population fam σ f).card ≤ S.card + 161 ∧
      ∀ z ∈ S, let q := (fam.q z).map σ
        let q' := chart r d q
        let f' := surfaceChart r W d f
        q'.natDegree ≤ d ∧ f'.eval₂ (evalRingHom (C (σ z))) q' = 0 ∧
          (f'.derivative.eval₂ (evalRingHom (C (σ z))) q').natDegree = W - d ∧
          ∀ i ∈ HalfPredecessorLineCoreGeometry.fullAgreement dom (u 0) (u 1) z (fam.q z),
            q'.eval ((σ (dom i) - r)⁻¹) =
              ((σ (dom i) - r)⁻¹) ^ d * σ (u 0 i) + σ z *
                (((σ (dom i) - r)⁻¹) ^ d * σ (u 1 i)) := by
  classical
  let d := 67108863
  let W := SecondPrimeCoordinateWeight.weight d f
  let M := population fam σ f
  let q := fun z => (fam.q z).map σ
  let R := fun z => f.derivative.eval₂ (evalRingHom (C (σ z))) (q z)
  let S := M.filter fun z => R z ≠ 0
  have hexc := SecondPrimeSectionResultant.secondPrime_multiple_section_cap σ f Q hchar hi hb
    hQ hdiv htri M q (fun _ hz => (mem_filter.mp hz).2)
  have hsize : M.card ≤ S.card + 161 := by
    have hs := M.card_filter_add_card_filter_not (fun z => R z = 0)
    change (M.filter fun z => R z = 0).card ≤ 161 at hexc
    have hS : (M.filter fun z => ¬R z = 0) = S := by ext; simp [S]
    rw [hS] at hs
    omega
  let e : I ↪ K := dom.trans ⟨σ, σ.injective⟩
  obtain ⟨r, hr, hall⟩ := common_center S (univ.map e) R (fun z hz => (mem_filter.mp hz).2)
  have hsite (i : I) : σ (dom i) ≠ r := fun he => hr (mem_map.mpr ⟨i, mem_univ i, he⟩)
  refine ⟨r, hsite, S, filter_subset _ _, hsize, ?_⟩
  intro z hz
  have hzM := (mem_filter.mp hz).1
  have hzG := (mem_filter.mp hzM).1
  have hd := fam.degree_lt z hzG
  have hq : (q z).natDegree ≤ d := natDegree_map_le.trans (by dsimp [d]; omega)
  let Fz := f.map (evalRingHom (C (σ z)))
  have hroot : Fz.eval (q z) = 0 := by simpa only [Fz, eval_map] using (mem_filter.mp hzM).2
  have hw := section_weight d f (σ z)
  refine ⟨chart_degree_le r d (q z) hq, ?_, ?_, ?_⟩
  · rw [← eval_map, surface_fiber, plane_graph _ _ _ _ _ hq hw, hroot, map_zero]
  · rw [← eval_map, ← derivative_map, surface_fiber]
    apply derivative_graph_degree _ _ _ _ _ hq hw
    simpa only [derivative_map, eval_map] using hall z hz
  · intro i hi'
    rw [chart_eval r (σ (dom i)) (hsite i) d _ hq, eval_map_apply, (mem_filter.mp hi').2,
      map_add, map_mul]
    ring

end ArkLib.ProximityGap.Frontier.SecondPrimeMobiusSections
