/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarFixedFactors

/-! # Sparse fibers of the trimmed moment pencil -/

open Finset Polynomial Matrix
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarPrimitiveKernel
open ProximityGap.ApolarMomentCoordinates ProximityGap.ApolarFixedFactors

namespace ProximityGap.ApolarSparseSpecialization

variable {K : Type*} [Field K]

/-- Sparse scalar moments remain sparse after extending the alphabet. -/
theorem extend_atoms {F : Type*} [Field F] (φ : F →+* K) (m : ℕ → F[X]) (t : F)
    (E : Finset F) (w : F → F) {d : ℕ}
    (h : ∀ j ≤ d, (m j).eval t=∑ y ∈ E, w y*y^j) :
    ∃ b : K → K, ∀ j ≤ d, ((m j).map φ).eval (φ t)=∑ y ∈ E.map
      ⟨φ,φ.injective⟩, b y*y^j := by
  let b := Function.extend φ (φ ∘ w) (fun _ => 0)
  refine ⟨b,?_⟩
  intro j hj
  rw [eval_map_apply,h j hj,map_sum,Finset.sum_map]
  apply sum_congr rfl
  intro y _
  simp only [Function.Embedding.coeFn_mk,map_mul,map_pow]
  rw [show b (φ y)=φ (w y) from φ.injective.extend_apply _ _ _]

/-- Evaluation in the parameter and in the coordinate commute. -/
theorem eval_commute (p : K[X][X]) (t y : K) :
    (p.eval (C y)).eval t = (p.map (evalRingHom t)).eval y := by
  have hh := eval₂_at_apply (p:=p) (evalRingHom t) (C y)
  simpa only [coe_evalRingHom,eval_C,←eval_map] using hh.symm

/-- Specializing arbitrary polynomial coefficients in a bounded locator commutes
with passing from its coefficient vector to its coordinate polynomial. -/
theorem form_specialize {s : ℕ} (v : Fin (s+1) → K[X]) (t : K) :
    (form v).map (evalRingHom t) = form (fun i => (v i).eval t) := by
  simp [form,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_pow]

/-- Exact sparse moments imply the same functional equality on every polynomial
whose degree is in the truncated range. -/
theorem atoms_apply (m : ℕ → K[X]) (t : K) (E : Finset K) (w : K → K) {d : ℕ}
    (ha : ∀ j ≤ d, (m j).eval t=∑ y ∈ E, w y*y^j)
    (p : K[X]) (hp : p.natDegree ≤ d) :
    ((functional m) (p.map C)).eval t = weighted E (RingHom.id K) w p := by
  apply Polynomial.induction_with_natDegree_le (fun q => ((functional m) (q.map C)).eval t=
    weighted E (RingHom.id K) w q) d (by simp) _ _ p hp
  · intro j a _ hj
    rw [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,← smul_eq_C_mul,
      map_smul,functional_X_pow,smul_eq_mul,eval_mul,eval_C,ha j hj,weighted_apply,Finset.mul_sum]
    apply sum_congr rfl
    intro y _
    simp only [RingHom.id_apply,eval_mul,eval_C,eval_pow,eval_X]
    ring
  · intro p q _ _ h₁ h₂
    simp only [map_add,Polynomial.map_add,eval_add,h₁,h₂]

/-- All nonzero atoms of a sufficiently sparse scalar specialization are roots
of the full polynomial kernel locator, in either coordinate order. -/
theorem site_is_root (m : ℕ → K[X]) {d s : ℕ} (hs : s ≤ d) (v : Fin (s+1) → K[X])
    (hk : catalecticant m d s *ᵥ v = 0) (t : K) (E : Finset K) (w : K → K)
    (hcard : E.card ≤ d-s+1) (ha : ∀ j ≤ d, (m j).eval t=∑ y ∈ E,w y*y^j)
    {y : K} (hy : y ∈ E) (hw : w y ≠ 0) : ((form v).eval (C y)).eval t = 0 := by
  classical
  let L := weighted E (RingHom.id K) w
  let b (i : Fin (s+1)) := (v i).eval t
  let μ (j : ℕ) := L (X^j)
  have hμ (j : ℕ) (hj : j ≤ d) : μ j=(m j).eval t := by
    simpa only [μ,L,weighted_apply,RingHom.id_apply,eval_pow,eval_X] using (ha j hj).symm
  have happ : ApolarThrough L (form b) (d-s) := by
    rw [←functional_moments L]
    apply (equations_iff_apolar μ b).mp
    intro j hj
    have hc := congrArg (Polynomial.eval t) (congrFun hk ⟨j,by omega⟩)
    change (∑ i : Fin (s+1), m (j+i.val)*v i).eval t = (0 : K[X]).eval t at hc
    rw [eval_finsetSum,eval_zero] at hc
    convert hc using 1
    apply sum_congr rfl
    intro i _
    rw [hμ _ (by have := i.isLt; omega),eval_mul]
  rw [eval_commute,form_specialize]
  exact isRoot_of_reduced E w (form b) hcard happ hy hw

/-- Trimming the domain vanisher preserves every surviving atom with its exact
new weight, removes all fixed and zero-weight sites, and forces the original
locator to vanish there. -/
theorem trimmed_atoms [DecidableEq K] (m : ℕ → K[X]) {d s : ℕ} (hs : s ≤ d)
    (v : Fin (s+1) → K[X]) (hk : catalecticant m d s *ᵥ v = 0) (H A E : Finset K)
    (t : K) (w : K → K) (hE : E ⊆ H) (hcard : E.card ≤ d-s+1)
    (ha : ∀ j ≤ d, (m j).eval t=∑ y ∈ E,w y*y^j) :
    ∃ U ⊆ H \ A, ∃ b : K → K,
      (∀ j, A.card+j ≤ d → ((trim (functional m) (Lagrange.nodal A id))
        (X^j)).eval t = ∑ y ∈ U, b y*y^j) ∧
      ∀ y ∈ U, ((form v).eval (C y)).eval t = 0 := by
  classical
  let U := (E \ A).filter (fun y => w y ≠ 0)
  let G := Lagrange.nodal A id
  refine ⟨U,fun y hy => mem_sdiff.mpr ⟨hE (mem_sdiff.mp (mem_filter.mp hy).1).1,
    (mem_sdiff.mp (mem_filter.mp hy).1).2⟩,fun y => w y*G.eval y,?_,?_⟩
  · intro j hj
    have hd : (G*X^j).natDegree ≤ d := by
      have h := natDegree_mul_le (p:=G) (q:=X^j)
      simpa only [G,Lagrange.natDegree_nodal,natDegree_X_pow] using
        h.trans (by simpa only [G,Lagrange.natDegree_nodal,natDegree_X_pow] using hj)
    have hh := atoms_apply m t E w ha (G*X^j) hd
    rw [show weighted E (RingHom.id K) w (G*X^j)=_ from weighted_nodal E A w (X^j)] at hh
    simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,weighted_apply,
      RingHom.id_apply,eval_pow,eval_X] at hh
    simp only [trim,LinearMap.comp_apply,LinearMap.mulLeft_apply]
    refine hh.trans ?_
    symm
    apply Finset.sum_subset (filter_subset _ _)
    intro y hy hny
    have hz : w y=0 := by simpa [U,hy] using hny
    simp [hz]
  · intro y hy
    exact site_is_root m hs v hk t E w hcard ha (mem_sdiff.mp (mem_filter.mp hy).1).1 (mem_filter.mp hy).2

open Code
open scoped NNReal

/-- Lift the entire family of actual sparse MCA specialized syndromes to the
geometric alphabet along the given embedding, preserving both support sizes. -/
theorem extended_mca_atoms {F L ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Field L] [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (φ : F →+* L) (dom : ι ↪ F) {k e d : ℕ} {δ : ℝ≥0}
    (u : WordStack F (Fin 2) ι) (bad : Finset F) (hk : 1 ≤ k) (hd : k+d < Fintype.card ι)
    (he : Fintype.card ι - e ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊)
    (hbad : ∀ t ∈ bad, mcaEvent (ReedSolomon.code dom k : Set (ι → F)) δ (u 0) (u 1) t) :
    let H := (univ : Finset ι).map dom
    let μ := fun j => (ApolarHankelMinors.moment H (ApolarMcaSyndrome.coordinateRow dom (u 0))
      (ApolarMcaSyndrome.coordinateRow dom (u 1)) j).map φ
    let ψ : F ↪ L := ⟨φ,φ.injective⟩
    ∀ t ∈ bad.map ψ, ∃ E ⊆ H.map ψ, E.card ≤ e ∧
      ∃ w : L → L, ∀ j ≤ d, (μ j).eval t = ∑ y ∈ E, w y*y^j := by
  classical
  intro H μ ψ t ht
  obtain ⟨b,hb,rfl⟩ := mem_map.mp ht
  obtain ⟨E,hE,hcard,w,hwa⟩ := ApolarMcaSyndrome.sparse_moments_of_mcaEvent
    dom hk hd he (hbad b hb)
  exact ⟨E.map ψ,Finset.map_subset_map.mpr hE,by simpa using hcard,extend_atoms φ _ b E w hwa⟩

#print axioms extended_mca_atoms
#print axioms trimmed_atoms
#print axioms extend_atoms

end ProximityGap.ApolarSparseSpecialization
