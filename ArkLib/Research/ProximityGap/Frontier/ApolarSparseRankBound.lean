/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarPencilNullity
import ArkLib.Research.ProximityGap.Frontier.ApolarPrimitiveKernel

/-! # A regular square moment minor counts all sparse fibers

A minimal generic apolar recurrence makes the preceding rectangular moment
matrix injective. A square minor supplies the full rank at an ordinary scalar.
Each sparse moment fiber factors through its weighted error support.
-/

set_option autoImplicit false
open Finset Polynomial Matrix
open ProximityGap.ApolarPrimitiveKernel
open ArkLib.ProximityGap.Frontier.ApolarPencilNullity
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.ApolarSparseRankBound

variable {K : Type*} [Field K] [Infinite K]

/-- Every injective polynomial matrix has a full square minor regular at an
ordinary scalar over an infinite coefficient field. -/
theorem regular_minor {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (D : Matrix I J K[X]) (hk : ∀ v, D *ᵥ v = 0 → v=0) :
    ∃ rows : J → I, ∃ t : K, ((D.submatrix rows id).map (evalRingHom t)).det ≠ 0 := by
  classical
  let φ := algebraMap K[X] (FractionRing K[X])
  have hfrac := AGL24.frac_kernel_trivial_of_poly_kernel_trivial D hk
  obtain ⟨rows,_,hn⟩ := AGL24.exists_square_submatrix_det_ne_zero (D.map φ) hfrac
  let M := D.submatrix rows id
  have hM : M.det ≠ 0 := by
    intro h
    apply hn
    change (M.map φ).det = 0
    rw [← RingHom.mapMatrix_apply,← RingHom.map_det,h,map_zero]
  obtain ⟨t,ht⟩ := Infinite.exists_notMem_finset M.det.roots.toFinset
  refine ⟨rows,t,?_⟩
  intro he
  apply ht
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots hM).mpr
  change (evalRingHom t) M.det = 0
  rw [RingHom.map_det]
  exact he

/-- A preceding injective moment matrix, sparse bad fibers, and the remaining
site locators give the full rank budget on the number of bad parameters. -/
theorem count_sparse_fibers (m : ℕ → K[X]) (d r : ℕ) (hr : r ≤ d)
    (ha : ∀ j ≤ d, (m j).natDegree ≤ 1)
    (hinj : ∀ v, catalecticant m d r *ᵥ v = 0 → v=0)
    (H S : Finset K) (E : K → Finset K) (w : K → K → K)
    (hs : ∀ t ∈ S, E t ⊆ H)
    (hw : ∀ t ∈ S, ∀ j ≤ d, (m j).eval t = ∑ x ∈ E t, w t x*x^j)
    (q : K → K[X]) (ℓ : ℕ) (hq : ∀ x ∈ H, q x ≠ 0 ∧ (q x).natDegree ≤ ℓ)
    (hz : ∀ t ∈ S, ∀ x ∈ E t, (q x).eval t = 0) :
    S.card*(r+1) ≤ H.card*ℓ+(r+1) := by
  classical
  let D := catalecticant m d r
  obtain ⟨rows,u,hu⟩ := regular_minor D hinj
  let A : Matrix (Fin (r+1)) (Fin (r+1)) K := fun i j => (m ((rows i).val+j.val)).coeff 0
  let B : Matrix (Fin (r+1)) (Fin (r+1)) K := fun i j => (m ((rows i).val+j.val)).coeff 1
  have hj (i j : Fin (r+1)) : (rows i).val+j.val ≤ d := by
    have hrow := (rows i).isLt
    have hcol := j.isLt
    omega
  have he (t : K) (i j : Fin (r+1)) :
      (A+t • B) i j = (m ((rows i).val+j.val)).eval t := by
    conv_rhs => rw [eq_X_add_C_of_natDegree_le_one (ha _ (hj i j))]
    change (m _).coeff 0 + t*(m _).coeff 1 = _
    simp only [eval_add,eval_mul,eval_C,eval_X]
    ring
  have hmat (t : K) : (D.submatrix rows id).map (evalRingHom t) = A+t • B := by
    ext i j
    exact (he t i j).symm
  rw [hmat] at hu
  have hRank (t : K) (ht : t ∈ S) : (A+t • B).rank ≤ (E t).card := by
    apply weighted_matrix_rank_le (E t) (w t) (fun i x => x^(rows i).val) (fun j x => x^j.val)
    intro i j
    rw [he,hw t ht _ (hj i j)]
    apply sum_congr rfl
    intro x _
    rw [pow_add,mul_assoc]
  simpa only [Fintype.card_fin] using support_incidence_bound A B S u hu H E ℓ q hs hRank hq hz

end ArkLib.ProximityGap.Frontier.ApolarSparseRankBound

#print axioms ArkLib.ProximityGap.Frontier.ApolarSparseRankBound.count_sparse_fibers
