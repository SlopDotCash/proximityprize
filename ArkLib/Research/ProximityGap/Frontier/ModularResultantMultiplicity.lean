/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SquareSpecialization
import ArkLib.ToMathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Int.Basic

/-! # Common factors modulo a prime give powers of the prime in the integer resultant -/

namespace ProximityGap.ModularResultantMultiplicity
open Finset Polynomial Matrix

/-- Each dimension lost on reduction modulo a prime contributes a factor of the
prime to an integer determinant. -/
theorem corank_dvd_det {I : Type*} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]
    (M : Matrix I I ℤ) :
    (p : ℤ)^(Fintype.card I-((Int.castRingHom (ZMod p)).mapMatrix M).rank) ∣ M.det := by
  classical
  let φ := Int.castRingHom (ZMod p)
  let A := φ.mapMatrix M
  let k := Fintype.card I - A.rank
  obtain ⟨V,U,e,hV,hU,hform⟩ := A.exists_rank_normal_form
  let lift (T : Matrix I I (ZMod p)) : Matrix I I ℤ := T.map (fun t => (t.val:ℤ))
  have reduce (T : Matrix I I (ZMod p)) : φ.mapMatrix (lift T)=T := by
    ext i j; simp [φ,lift,RingHom.mapMatrix_apply]
  let N := lift V * M * lift U
  have hN : φ.mapMatrix N = (fromBlocks 1 0 0 0).submatrix e e := by
    simpa only [N,map_mul,reduce,A] using hform
  let S := (univ : Finset (Fin k)).map
    ((Function.Embedding.inr : Fin k ↪ _).trans e.symm.toEmbedding)
  have cols (j : I) (hj : j∈S) (i : I) : (p:ℤ) ∣ N i j := by
    obtain ⟨s,_,rfl⟩ := mem_map.mp hj
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change φ.mapMatrix N i (e.symm (.inr s))=0
    rw [hN]
    cases hi : e i <;> simp [Matrix.submatrix,hi,Matrix.fromBlocks]
  have detN := Matrix.pow_dvd_det_of_forall_mem_col_dvd N (p:ℤ) S cols
  have unitDet (T : Matrix I I (ZMod p)) (hT : IsUnit T) : ¬(p:ℤ) ∣ (lift T).det := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change φ (lift T).det ≠ 0
    rw [φ.map_det,reduce]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hT).ne_zero
  have prime := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have mul : (p:ℤ)^k ∣ M.det * ((lift V).det * (lift U).det) := by
    simpa only [S,card_map,card_univ,Fintype.card_fin,N,det_mul,mul_assoc,mul_left_comm,mul_comm]
      using detN
  exact prime.pow_dvd_of_dvd_mul_right _ (prime.not_dvd_mul (unitDet _ hV) (unitDet _ hU)) mul

/-- A common factor of the two modular reductions contributes its full degree
to the prime valuation of the integer resultant, even at padded degrees. -/
theorem common_factor {p : ℕ} [Fact p.Prime] (F G : ℤ[X]) {m n : ℕ}
    (hF : F.natDegree≤m) (hG : G.natDegree≤n)
    (W : (ZMod p)[X]) (hne : W≠0) (size : W.natDegree≤m+n)
    (hWF : W ∣ F.map (Int.castRingHom (ZMod p))) (hWG : W ∣ G.map (Int.castRingHom (ZMod p))) :
    (p:ℤ)^W.natDegree ∣ F.resultant G m n := by
  let φ := Int.castRingHom (ZMod p)
  have rank := SquareSpecialization.sylvester_rank_of_common_divisor (F.map φ) (G.map φ) W
    (natDegree_map_le.trans hF) (natDegree_map_le.trans hG) hne size hWF hWG
  have div := corank_dvd_det (p:=p) (sylvester F G m n)
  rw [← sylvester_map_map,Fintype.card_fin] at div
  dsimp [φ] at rank
  apply dvd_trans (pow_dvd_pow _ ?_) div
  omega

/-- Two distinct shared residue-field roots force the square of the prime to
divide the integer resultant. -/
theorem two_roots {p : ℕ} [Fact p.Prime] (F G : ℤ[X]) {m n : ℕ}
    (hF : F.natDegree≤m) (hG : G.natDegree≤n) (size : 2≤m+n)
    {a b : ZMod p} (distinct : a ≠ b)
    (fA : (F.map (Int.castRingHom (ZMod p))).eval a=0)
    (fB : (F.map (Int.castRingHom (ZMod p))).eval b=0)
    (gA : (G.map (Int.castRingHom (ZMod p))).eval a=0)
    (gB : (G.map (Int.castRingHom (ZMod p))).eval b=0) : (p:ℤ)^2 ∣ F.resultant G m n := by
  let W : (ZMod p)[X] := (X-C a)*(X-C b)
  have deg : W.natDegree=2 := by
    simp [W,natDegree_mul (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)]
  have cop := isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr distinct).isUnit
  rw [← deg]
  exact common_factor F G hF hG W (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))
    (deg ▸ size) (cop.mul_dvd (dvd_iff_isRoot.mpr fA) (dvd_iff_isRoot.mpr fB))
    (cop.mul_dvd (dvd_iff_isRoot.mpr gA) (dvd_iff_isRoot.mpr gB))

end ProximityGap.ModularResultantMultiplicity
#print axioms ProximityGap.ModularResultantMultiplicity.common_factor
#print axioms ProximityGap.ModularResultantMultiplicity.two_roots
