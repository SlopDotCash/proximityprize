/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.AGL24NonzeroMinor
import ArkLib.ToMathlib.PolynomialMatrixKernel
import Mathlib.LinearAlgebra.Lagrange
import ArkLib.Research.ProximityGap.Frontier.ApolarMcaSyndrome

/-! # Polynomial apolar locators from many sparse specializations

Each scalar specialization has a locator from its error sites. A full-column
minor has parameter degree at most the number of columns, so more scalar
roots force a common nonzero polynomial kernel vector.
-/

set_option autoImplicit false
open Polynomial Matrix Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.ApolarPencilExtraction

variable {K : Type*} [Field K]

/-- Any affine polynomial matrix whose scalar specializations are singular at
more points than it has columns admits a polynomial kernel vector. -/
theorem polynomial_kernel_of_many_specializations
    {I J : Type*} [Fintype I] [Fintype J] (M : Matrix I J K[X])
    (s : Finset K) (hs : Fintype.card J < s.card) (hdeg : ∀ i j, (M i j).natDegree ≤ 1)
    (hk : ∀ t ∈ s, ∃ v : J → K, v ≠ 0 ∧ (M.map (Polynomial.evalRingHom t)).mulVec v = 0) :
    ∃ v : J → K[X], v ≠ 0 ∧ M.mulVec v = 0 := by
  classical
  by_contra! hno
  let ϕ := algebraMap K[X] (FractionRing K[X])
  have hfrac := AGL24.frac_kernel_trivial_of_poly_kernel_trivial M
    (fun v hv => by by_contra h; exact hno v h hv)
  obtain ⟨rows, _, hdet⟩ := AGL24.exists_square_submatrix_det_ne_zero (M.map ϕ) hfrac
  let A := M.submatrix rows id
  have hA : A.det = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := (Subtype.val : s → K))
      Subtype.val_injective
    · intro t
      obtain ⟨v, hv, hMv⟩ := hk t.val t.property
      have hAv : (A.map (Polynomial.evalRingHom t.val)).mulVec v = 0 := by
        funext j
        exact congrFun hMv (rows j)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
      have hsing := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
        hAv (i := j) (mem_nonZeroDivisors_of_ne_zero hj)
      change (Polynomial.evalRingHom t.val) A.det = 0
      rw [RingHom.map_det]
      exact hsing
    · have hd := Polynomial.natDegree_det_le A (fun i j => hdeg (rows i) j)
      simpa using hd.trans_lt (by simpa using hs)
  apply hdet
  change (A.map ϕ).det = 0
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hA, map_zero]

/-- A sparse scalar moment sequence satisfies the recurrence of its vanisher
padded with zero coefficients to length \(e+1\). -/
theorem sparse_hankel_kernel (m : ℕ → K[X]) (d e : ℕ) (hed : e ≤ d) (t : K)
    (E : Finset K) (w : K → K) (hE : E.card ≤ e)
    (hMom : ∀ j ≤ d, (m j).eval t = ∑ x ∈ E, w x * x ^ j) :
    ∃ v : Fin (e+1) → K, v ≠ 0 ∧ ∀ j < d-e+1,
      ∑ i : Fin (e+1), (m (j+i.val)).eval t * v i = 0 := by
  classical
  let f := Lagrange.nodal E (id : K → K)
  have hfdeg : f.natDegree = E.card := Lagrange.natDegree_nodal
  let v : Fin (e+1) → K := fun i => f.coeff i.val
  refine ⟨v, ?_, ?_⟩
  · intro hzero
    have hc := congrFun hzero (⟨f.natDegree, by omega⟩ : Fin (e+1))
    change f.coeff f.natDegree = 0 at hc
    exact (Polynomial.leadingCoeff_ne_zero.mpr Lagrange.nodal_ne_zero) hc
  · intro j hj
    have heval (x : K) (hx : x ∈ E) : ∑ i : Fin (e+1), f.coeff i.val * x ^ i.val = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => f.coeff a * x ^ a) (e+1),
        ← Polynomial.eval_eq_sum_range' (p := f) (by omega)]
      exact Lagrange.eval_nodal_at_node (v := id) hx
    calc
      _ = ∑ i : Fin (e+1), ∑ x ∈ E, w x * x^j * (f.coeff i.val * x^i.val) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hMom (j+i.val) (by have := i.isLt; omega), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        dsimp only [v]
        rw [pow_add]
        ring
      _ = ∑ x ∈ E, w x * x^j * (∑ i : Fin (e+1), f.coeff i.val * x^i.val) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = 0 := Finset.sum_eq_zero (fun x hx => by rw [heval x hx, mul_zero])

/-- If more than \(e+1\) specializations of an affine syndrome pencil are
supported on at most \(e\) sites, its truncated Hankel matrix has a nonzero
polynomial recurrence. The support and weights may vary with the scalar. -/
theorem generic_locator_of_sparse_fibers (m : ℕ → K[X]) (d e : ℕ) (hed : e ≤ d)
    (s : Finset K) (hs : e+1 < s.card) (hdeg : ∀ j ≤ d, (m j).natDegree ≤ 1)
    (hSparse : ∀ t ∈ s, ∃ (E : Finset K) (w : K → K), E.card ≤ e ∧
      ∀ j ≤ d, (m j).eval t = ∑ x ∈ E, w x * x ^ j) :
    ∃ c : Fin (e+1) → K[X], c ≠ 0 ∧ ∀ j < d-e+1,
      ∑ i : Fin (e+1), m (j+i.val) * c i = 0 := by
  classical
  let M : Matrix (Fin (d-e+1)) (Fin (e+1)) K[X] := fun j i => m (j.val+i.val)
  have hm (j : Fin (d-e+1)) (i : Fin (e+1)) := hdeg (j.val+i.val)
    (by have := j.isLt; have := i.isLt; omega)
  obtain ⟨c, hc, hker⟩ := polynomial_kernel_of_many_specializations M s (by simpa using hs)
    hm (fun t ht => by
      obtain ⟨E, w, hE, hw⟩ := hSparse t ht
      obtain ⟨v, hv, hrec⟩ := sparse_hankel_kernel m d e hed t E w hE hw
      exact ⟨v, hv, funext fun j => hrec j.val j.isLt⟩)
  exact ⟨c, hc, fun j hj => congrFun hker (⟨j,hj⟩ : Fin (d-e+1))⟩


open Code _root_.ProximityGap
open _root_.ProximityGap.ApolarMcaSyndrome _root_.ProximityGap.ApolarHankelMinors
open scoped NNReal

/-- More than \(e+1\) actual MCA-bad scalars produce a common polynomial
recurrence for the received pair's own syndrome moments. -/
theorem generic_locator_of_mca_events {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (dom : ι ↪ F) {k e d : ℕ} {δ : ℝ≥0}
    (u : WordStack F (Fin 2) ι) (s : Finset F) (hs : e+1 < s.card)
    (hed : e ≤ d) (hk : 1 ≤ k) (hd : k+d < Fintype.card ι)
    (he : Fintype.card ι - e ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊)
    (hbad : ∀ t ∈ s, mcaEvent (ReedSolomon.code dom k : Set (ι → F)) δ (u 0) (u 1) t) :
    let H := (univ : Finset ι).map dom
    let m := moment H (coordinateRow dom (u 0)) (coordinateRow dom (u 1))
    ∃ c : Fin (e+1) → F[X], c ≠ 0 ∧ ∀ j < d-e+1,
      ∑ i : Fin (e+1), m (j+i.val) * c i = 0 := by
  classical
  dsimp only
  apply generic_locator_of_sparse_fibers _ d e hed s hs
  · intro j _
    unfold moment
    rw [Polynomial.natDegree_add_C]
    exact le_trans (Polynomial.natDegree_mul_C_le _ _) (le_of_eq Polynomial.natDegree_X)
  · intro t ht
    obtain ⟨E, _, hE, w, hw⟩ := sparse_moments_of_mcaEvent dom hk hd he (hbad t ht)
    exact ⟨E,w,hE,hw⟩

end ArkLib.ProximityGap.Frontier.ApolarPencilExtraction

#print axioms ArkLib.ProximityGap.Frontier.ApolarPencilExtraction.polynomial_kernel_of_many_specializations
#print axioms ArkLib.ProximityGap.Frontier.ApolarPencilExtraction.generic_locator_of_sparse_fibers

#print axioms ArkLib.ProximityGap.Frontier.ApolarPencilExtraction.generic_locator_of_mca_events
