/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SylvesterLocalMultiplicity
import ArkLib.Data.Polynomial.ResultantDegree
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # A Sylvester rank bound for square specializations -/

open Finset Polynomial Matrix

namespace ProximityGap.SquareSpecialization

variable {K : Type*} [Field K]

/-- The corank of a polynomial matrix at a parameter is a lower bound on the
order of vanishing of its determinant there. -/
theorem corank_dvd_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K[X]) (z : K) :
    (Polynomial.X - C z)^(Fintype.card ι - (M.map (eval z)).rank) ∣ M.det := by
  classical
  let A := M.map (eval z)
  let k := Fintype.card ι - A.rank
  obtain ⟨V,U,e,hV,hU,hform⟩ := A.exists_rank_normal_form
  let N := V.map C * M * U.map C
  let π := Polynomial.X-C z
  have hN : N.map (eval z) = (Matrix.fromBlocks 1 0 0 0).submatrix e e := by
    change (evalRingHom z).mapMatrix N = _
    simp only [N,map_mul]
    simpa [RingHom.mapMatrix,Matrix.map_map,Function.comp_def,A] using hform
  have hentry (i : Fin k) (j : ι) : π ∣ N j (e.symm (.inr i)) := by
    apply dvd_iff_isRoot.mpr
    have he := congrArg (fun B : Matrix ι ι K => B j (e.symm (.inr i))) hN
    change (N j (e.symm (.inr i))).eval z = _
    cases hj : e j <;> simpa [Matrix.submatrix,hj,Matrix.fromBlocks] using he
  have hdet : π^k ∣ N.det := by
    rw [Matrix.det_apply]
    apply Finset.dvd_sum
    intro σ _
    have hprod : π^k ∣ ∏ j, N (σ j) j := by
      rw [← Equiv.prod_comp e.symm (fun j : ι => N (σ j) j), Fintype.prod_sum_type]
      apply dvd_mul_of_dvd_right
      have h := prod_dvd_prod_of_dvd _ _ (fun (i : Fin k) (_ : i ∈ univ) => hentry i (σ (e.symm (.inr i))))
      simpa using h
    obtain ⟨w,hw⟩ := hprod
    exact ⟨Equiv.Perm.sign σ • w, by rw [hw,mul_smul_comm]⟩
  change π^k ∣ M.det
  have hV' : IsUnit (V.map (C (R := K))).det := by
    exact (Matrix.isUnit_iff_isUnit_det _).mp (hV.map (C (R := K)).mapMatrix)
  have hU' : IsUnit (U.map (C (R := K))).det := by
    exact (Matrix.isUnit_iff_isUnit_det _).mp (hU.map (C (R := K)).mapMatrix)
  simpa only [N,Matrix.det_mul,hU'.dvd_mul_right,hV'.dvd_mul_left] using hdet

/-- A common polynomial divisor gives at least its degree in Sylvester corank,
also for an explicitly padded matrix. -/
theorem sylvester_rank_of_common_divisor (f g W : K[X]) {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hW : W ≠ 0)
    (hWm : W.natDegree ≤ m+n) (hWf : W ∣ f) (hWg : W ∣ g) :
    (sylvester f g m n).rank ≤ m+n-W.natDegree := by
  classical
  let k := m+n-W.natDegree
  let J : degreeLT K k →ₗ[K] degreeLT K (m+n) := {
    toFun := fun p => ⟨W*p.val, by
      by_cases hp : p.val = 0
      · simp [hp]
      apply mem_degreeLT.mpr
      apply (natDegree_lt_iff_degree_lt (mul_ne_zero hW hp)).mp
      rw [natDegree_mul hW hp]
      have h := (natDegree_lt_iff_degree_lt hp).mpr (mem_degreeLT.mp p.property)
      dsimp [k] at h
      omega⟩
    map_add' := by intro x y; ext1; exact mul_add _ _ _
    map_smul' := by intro a x; ext1; exact mul_smul_comm _ _ _ }
  let S := sylvesterMap f g hf hg
  have hsub : LinearMap.range S ≤ LinearMap.range J := by
    rintro y ⟨p,rfl⟩
    have hdiv : W ∣ (S p).val := dvd_add (dvd_mul_of_dvd_left hWf _) (dvd_mul_of_dvd_left hWg _)
    obtain ⟨q,hq⟩ := hdiv
    refine ⟨⟨q,?_⟩,Subtype.ext hq.symm⟩
    by_cases hq0 : q = 0
    · simp [hq0]
    apply mem_degreeLT.mpr
    apply (natDegree_lt_iff_degree_lt hq0).mp
    have hsp := mem_degreeLT.mp (S p).property
    rw [hq, ← natDegree_lt_iff_degree_lt (mul_ne_zero hW hq0), natDegree_mul hW hq0] at hsp
    dsimp [k]; omega
  let b1 := ((degreeLT.basis K m).prod (degreeLT.basis K n)).reindex finSumFinEquiv
  let b2 := degreeLT.basis K (m+n)
  have hM : S.toMatrix b1 b2 = sylvester f g m n := toMatrix_sylvesterMap' f g hf hg
  have hr := (sylvester f g m n).rank_eq_finrank_range_toLin b2 b1
  rw [← hM,Matrix.toLin_toMatrix] at hr
  rw [← hM,hr]
  have hk : Module.finrank K (degreeLT K k) = k := by
    simpa using Module.finrank_eq_card_basis (degreeLT.basis K k)
  have h1 := Submodule.finrank_mono hsub
  have h2 := J.finrank_range_add_finrank_ker
  omega

/-- A coordinate polynomial with nonzero derivative resultant can specialize to
a square up to a scalar, retaining its degree, at at most four times its
parameter degree many distinct parameter values. -/
theorem card_regular_squares_le (H : Polynomial K[X]) (S : Finset K)
    (hr : 0 < H.natDegree)
    (hRes : resultant H H.derivative H.natDegree (H.natDegree-1) ≠ 0)
    (hS : ∀ z ∈ S, (H.map (evalRingHom z)).natDegree = H.natDegree ∧
      ∃ (c : K) (W : K[X]), H.map (evalRingHom z) = C c * W^2) :
    S.card ≤ 4*Bivariate.degreeX H := by
  classical
  let r := H.natDegree
  let n := r-1
  let M := sylvester H H.derivative r n
  let v (z : K) := r+n-(M.map (eval z)).rank
  have hval (z : K) : (Polynomial.X-C z)^(v z) ∣ resultant H H.derivative r n := by
    simpa only [v,Fintype.card_fin,M,resultant] using corank_dvd_det M z
  have hs (z : K) (hz : z ∈ S) : r ≤ 2*v z := by
    obtain ⟨hdeg,c,W,hW⟩ := hS z hz
    have hne : H.map (evalRingHom z) ≠ 0 := by
      intro he; rw [he,natDegree_zero] at hdeg; omega
    have hc : c ≠ 0 := by intro he; simp [he] at hW; exact hne hW
    have hw : W ≠ 0 := by intro he; simp [he] at hW; exact hne hW
    have hd : 2*W.natDegree = r := by
      rw [hW,natDegree_C_mul hc,natDegree_pow] at hdeg
      exact hdeg
    have hw1 : W ∣ H.map (evalRingHom z) := by
      rw [hW,pow_two]; exact ⟨C c*W, by ring⟩
    have hw2 : W ∣ H.derivative.map (evalRingHom z) := by
      rw [← derivative_map,hW,derivative_C_mul,derivative_pow]
      refine ⟨C c * C 2 * W.derivative,?_⟩
      simp
      ring
    have hsyl := sylvester_rank_of_common_divisor (H.map (evalRingHom z))
      (H.derivative.map (evalRingHom z)) W (m := r) (n := n) (natDegree_map_le)
      (natDegree_map_le.trans (natDegree_derivative_le H)) hw (by omega) hw1 hw2
    rw [sylvester_map_map] at hsyl
    change (M.map (eval z)).rank ≤ r+n-W.natDegree at hsyl
    dsimp only [v]; omega
  have hsum := Finset.sum_le_sum hs
  rw [sum_const, nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum] at hsum
  have hord := ArkLib.ProximityGap.Frontier.SylvesterLocalMultiplicity.sum_local_orders_le_natDegree
    _ hRes S v (fun z _ => hval z)
  have hbound := natDegree_resultant_derivative_padded_le H
  have hbudget := hsum.trans (Nat.mul_le_mul_left 2 (hord.trans hbound))
  change S.card*r ≤ 2*((2*r-1)*Bivariate.degreeX H) at hbudget
  have hle := Nat.mul_le_mul_right (Bivariate.degreeX H) (Nat.sub_le (2*r) 1)
  by_contra! hlarge
  have hgt := Nat.mul_lt_mul_of_pos_right hlarge hr
  change 4*Bivariate.degreeX H*r < S.card*r at hgt
  nlinarith

#print axioms corank_dvd_det
#print axioms sylvester_rank_of_common_divisor
#print axioms card_regular_squares_le

end ProximityGap.SquareSpecialization
