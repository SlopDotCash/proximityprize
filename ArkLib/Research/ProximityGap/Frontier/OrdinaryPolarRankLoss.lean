/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.PolynomialSectionJacobian
import ArkLib.ToMathlib.LinearAlgebra.Matrix.Determinant
import ArkLib.Research.ProximityGap.Frontier.SylvesterLocalMultiplicity
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/-! # Section divisibility and rank loss for ordinary first polars

A section gives two copies of its derivative divisor in the first polar
resultant. A specialized square polynomial matrix loses at least as many
orders of its determinant as the nullity of its specialization.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset Matrix
open scoped BigOperators Differential

namespace ArkLib.ProximityGap.Frontier.OrdinaryPolarRankLoss

variable {A : Type*} [CommRing A] [IsDomain A] [Differential A]

/-- The residual factor of the section contributes the second copy, via the
padded Bézout identity. Scalar specialization may lower the value degrees. -/
theorem section_square_dvd_polar (q c : A) (F G : A[X]) (m n : ℕ)
    (hF : F = (X-C q)*G) (hm : 1+G.natDegree ≤ m) (hn0 : n ≠ 0)
    (hn : (Differential.mapCoeffs F + C c*F.derivative).natDegree ≤ n) :
    G.eval q ^ 2 ∣ F.resultant (Differential.mapCoeffs F + C c*F.derivative) m n := by
  let T := Differential.mapCoeffs F + C c*F.derivative
  have ht : G.eval q ∣ T.eval q := by
    obtain ⟨hx,hy⟩ := PolynomialSectionJacobian.section_partials q G F hF
    exact ⟨c-q′, by simp only [T,eval_add,eval_mul,eval_C,hx,hy]; ring⟩
  obtain ⟨a,b,_,_,hab⟩ := exists_mul_add_mul_eq_C_resultant G T le_rfl hn (Or.inr hn0)
  have hres : G.eval q ∣ G.resultant T G.natDegree n := by
    have he := congrArg (Polynomial.eval q) hab
    rw [eval_add, eval_mul, eval_mul, eval_C] at he
    rw [← he]
    exact dvd_add (dvd_mul_right ..) (dvd_mul_of_dvd_left ht _)
  have hh : ((X-C q)*G).natDegree ≤ 1+G.natDegree :=
    natDegree_mul_le.trans (Nat.add_le_add_right (natDegree_X_sub_C_le q) _)
  change G.eval q ^ 2 ∣ F.resultant T m n
  conv_rhs => rw [hF]
  rw [show m = (1+G.natDegree)+(m-(1+G.natDegree)) by omega,
    resultant_add_left_deg _ _ _ _ _ hh]
  apply dvd_mul_of_dvd_right
  have H := resultant_mul_left (X-C q) G T n hn
  rw [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ hn] at H
  rw [H,pow_two]
  exact mul_dvd_mul ht hres

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- A square polynomial matrix loses determinant order at least equal to the
nullity over the residue field, without a generic nonsingularity hypothesis. -/
theorem specialization_nullity_dvd (M : Matrix ι ι K[X]) (z : K) :
    (X-C z)^(Fintype.card ι - (M.map (evalRingHom z)).rank) ∣ M.det := by
  classical
  let Mz := M.map (evalRingHom z)
  obtain ⟨V,U,e,hV,hU,hnf⟩ := Mz.exists_rank_normal_form
  let L := V.map (C : K →+* K[X])
  let R := U.map (C : K →+* K[X])
  let B := L*M*R
  have hmap (Q : Matrix ι ι K) : (Q.map (C : K →+* K[X])).map (evalRingHom z) = Q := by
    ext i j
    simp
  have hb : B.map (evalRingHom z) = (Matrix.fromBlocks 1 0 0 0).submatrix e e := by
    change (evalRingHom z).mapMatrix (L*M*R) = _
    rw [map_mul, map_mul]
    change (L.map (evalRingHom z))*Mz*(R.map (evalRingHom z)) = _
    simpa only [L,R,hmap] using hnf
  let S := Finset.univ.filter (fun j : ι => (e j).isRight)
  have hc : S.card = Fintype.card ι - Mz.rank := by
    let emb : Fin (Fintype.card ι - Mz.rank) ↪ ι :=
      ⟨fun j => e.symm (.inr j), e.symm.injective.comp Sum.inr_injective⟩
    have hs : S = Finset.univ.map emb := by
      ext i
      simp only [S, mem_filter, mem_univ, true_and, mem_map, emb]
      cases h : e i with
      | inl j => simp [← e.apply_eq_iff_eq, h]
      | inr j => exact ⟨fun _ => ⟨j, e.symm_apply_eq.mpr h.symm⟩, fun _ => rfl⟩
    simp [hs]
  have hd : (X-C z)^S.card ∣ B.det := by
    apply Matrix.pow_dvd_det_of_forall_mem_col_dvd
    intro j hj i
    apply dvd_iff_isRoot.mpr
    change B.map (evalRingHom z) i j = 0
    rw [hb]
    have hj' : (e j).isRight := (mem_filter.mp hj).2
    cases h : e j <;> cases g : e i <;> simp_all [Matrix.submatrix_apply]
  have hLV : IsUnit L.det := by
    rw [show L.det = C V.det from (C.map_det V).symm]
    exact ((Matrix.isUnit_iff_isUnit_det V).mp hV).map _
  have hRU : IsUnit R.det := by
    rw [show R.det = C U.det from (C.map_det U).symm]
    exact ((Matrix.isUnit_iff_isUnit_det U).mp hU).map _
  rw [hc,show B.det = L.det*M.det*R.det by simp [B,Matrix.det_mul]] at hd
  exact hLV.dvd_mul_left.mp (hRU.dvd_mul_right.mp hd)

omit [Fintype ι] [DecidableEq ι] in
/-- A shared specialized factor of degree h cuts h dimensions out of the
Sylvester image. No assertion about the full kernel or the specialized degrees is needed. -/
theorem rank_add_common_degree_le (f g Q : K[X]) (m n : ℕ) (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n) (hQ : Q.Monic) (hp : 0 < Q.natDegree)
    (hh : Q.natDegree ≤ m+n) (hqf : Q ∣ f) (hqg : Q ∣ g) :
    (sylvester f g m n).rank + Q.natDegree ≤ m+n := by
  let π := (AdjoinRoot.mkₐ Q).toLinearMap.comp (degreeLT K (m+n)).subtype
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective x
    have hr := natDegree_modByMonic_lt p hQ (by rintro rfl; simp at hp)
    refine ⟨⟨p %ₘ Q, mem_degreeLT.mpr (degree_le_natDegree.trans_lt (by exact_mod_cast hr.trans_le hh))⟩,?_⟩
    change AdjoinRoot.mk Q (p %ₘ Q) = AdjoinRoot.mk Q p
    simpa only [AdjoinRoot.modByMonicHom_mk] using AdjoinRoot.mk_leftInverse hQ (AdjoinRoot.mk Q p)
  let L := sylvesterMap f g hf hg
  have hle : LinearMap.range L ≤ LinearMap.ker π := by
    rintro _ ⟨z,rfl⟩
    change AdjoinRoot.mk Q (f * z.2.val + g * z.1.val) = 0
    exact AdjoinRoot.mk_eq_zero.mpr (dvd_add (dvd_mul_of_dvd_left hqf _) (dvd_mul_of_dvd_left hqg _))
  have hd := Submodule.finrank_mono hle
  have hk := π.finrank_range_add_finrank_ker
  have htop := LinearMap.range_eq_top.mpr hπ
  rw [htop,finrank_top] at hk
  have hdQ : Module.finrank K (AdjoinRoot Q) = Q.natDegree := finrank_quotient_span_eq_natDegree
  have hw : Module.finrank K (degreeLT K (m+n)) = m+n := by
    simpa using Module.finrank_eq_card_basis (degreeLT.basis K (m+n))
  rw [hdQ,hw] at hk
  have hrank : (sylvester f g m n).rank = Module.finrank K (LinearMap.range L) := by
    let b₁ := ((degreeLT.basis K m).prod (degreeLT.basis K n)).reindex finSumFinEquiv
    let b₂ := degreeLT.basis K (m+n)
    rw [Matrix.rank_eq_finrank_range_toLin _ b₂ b₁, ← toMatrix_sylvesterMap' f g hf hg]
    exact congrArg (fun T => Module.finrank K (LinearMap.range T)) (Matrix.toLin_toMatrix b₁ b₂ L)
  omega

/-- A common factor of a specialized pair costs its entire degree as a root
multiplicity of the generic resultant. The generic resultant may be padded. -/
theorem specialization_factor_dvd (F G : K[X][X]) (z : K) (Q : K[X]) (m n : ℕ)
    (hf : F.natDegree ≤ m) (hg : G.natDegree ≤ n) (hQ : Q.Monic)
    (hp : 0 < Q.natDegree) (hh : Q.natDegree ≤ m+n)
    (hQF : Q ∣ F.map (evalRingHom z)) (hQG : Q ∣ G.map (evalRingHom z)) :
    (X-C z)^Q.natDegree ∣ F.resultant G m n := by
  have h := specialization_nullity_dvd (sylvester F G m n) z
  have hr := rank_add_common_degree_le _ _ _ _ _ ((natDegree_map_le ..).trans hf)
    ((natDegree_map_le ..).trans hg) hQ hp hh hQF hQG
  rw [sylvester_map_map] at hr
  apply dvd_trans (pow_dvd_pow _ ?_) h
  simpa [RingHom.mapMatrix_apply] using Nat.le_sub_of_add_le' hr


/-- After dividing out the integral generic common factor E, two specialized
copies of the section divisor still charge at least 2J−deg E orders to the
residual resultant. Both residuals may vanish in a special fiber. -/
theorem residual_specialization (F G : K[X][X]) (z : K) (E q : K[X]) (u : ℕ)
    (hf : F.natDegree ≤ u) (hg : G.natDegree ≤ u) (he : E ≠ 0) (hq : q ≠ 0)
    (hsize : 2*q.natDegree-E.natDegree ≤ u+u)
    (ha : q^2 ∣ E*(F.map (evalRingHom z))) (hb : q^2 ∣ E*(G.map (evalRingHom z))) :
    (X-C z)^(2*q.natDegree-E.natDegree) ∣ F.resultant G u u := by
  classical
  let f := F.map (evalRingHom z)
  let g := G.map (evalRingHom z)
  by_cases h : f = 0 ∧ g = 0
  · have h0 := specialization_nullity_dvd (sylvester F G u u) z
    have hs : (sylvester F G u u).map (evalRingHom z) = 0 := by
      change (evalRingHom z).mapMatrix _ = 0
      rw [← sylvester_map_map]
      change sylvester f g u u = 0
      rw [h.1,h.2]
      ext i j
      simp [sylvester, Fin.addCases]
    rw [hs, Matrix.rank_zero, Fintype.card_fin, Nat.sub_zero] at h0
    exact (pow_dvd_pow _ hsize).trans h0
  let d := GCDMonoid.gcd f g
  have hd : d ≠ 0 := by simpa [d, _root_.gcd_eq_zero_iff] using h
  have hdv : q^2 ∣ E*d := (dvd_gcd ha hb).trans (gcd_mul_left' E f g).dvd
  have hdeg := natDegree_le_of_dvd hdv (mul_ne_zero he hd)
  rw [natDegree_pow, natDegree_mul he hd] at hdeg
  let Q := normalize d
  have hdQ : Q.natDegree = d.natDegree := natDegree_normalize
  have hQF : Q ∣ f := (associated_normalize d).symm.dvd.trans (gcd_dvd_left ..)
  have hQG : Q ∣ g := (associated_normalize d).symm.dvd.trans (gcd_dvd_right ..)
  have hle : Q.natDegree ≤ u+u := by
    by_cases hf0 : f = 0
    · have hg0 : g ≠ 0 := fun h0 => h ⟨hf0,h0⟩
      exact (natDegree_le_of_dvd hQG hg0).trans ((natDegree_map_le ..).trans (by omega : G.natDegree ≤ u+u))
    · exact (natDegree_le_of_dvd hQF hf0).trans ((natDegree_map_le ..).trans (by omega : F.natDegree ≤ u+u))
  by_cases hp : 0 < Q.natDegree
  · exact (pow_dvd_pow _ (by omega : 2*q.natDegree-E.natDegree ≤ Q.natDegree)).trans
      (specialization_factor_dvd F G z Q u u hf hg (monic_normalize hd) hp hle hQF hQG)
  · simp [show 2*q.natDegree-E.natDegree = 0 by omega]

/-- Sum the double-section charges over distinct scalar fibers of the residual
resultant. Its scalar degree controls the loss from persistent intersections. -/
theorem residual_degree_budget (F G : K[X][X]) (S : Finset K) (E q : K → K[X])
    (u J w : ℕ) (hf : F.natDegree ≤ u) (hg : G.natDegree ≤ u)
    (hR : F.resultant G u u ≠ 0)
    (hdeg : ∀ z ∈ S, (q z).natDegree = J ∧ (E z).natDegree ≤ w)
    (hn : ∀ z ∈ S, E z ≠ 0 ∧ q z ≠ 0)
    (hs : ∀ z ∈ S, 2*J-(E z).natDegree ≤ u+u)
    (ha : ∀ z ∈ S, q z^2 ∣ E z*(F.map (evalRingHom z)))
    (hb : ∀ z ∈ S, q z^2 ∣ E z*(G.map (evalRingHom z))) :
    S.card*(2*J-w) ≤ (F.resultant G u u).natDegree := by
  have H := SylvesterLocalMultiplicity.sum_local_orders_le_natDegree _ hR S (fun _ => 2*J-w) (by
    intro z hz
    obtain ⟨hq,he⟩ := hdeg z hz
    apply dvd_trans (pow_dvd_pow _ (by omega : 2*J-w ≤ 2*(q z).natDegree-(E z).natDegree))
    exact residual_specialization F G z _ _ u hf hg (hn z hz).1 (hn z hz).2
      (by simpa [hq] using hs z hz) (ha z hz) (hb z hz))
  simpa using H

#print axioms residual_degree_budget

#print axioms rank_add_common_degree_le
#print axioms specialization_factor_dvd

#print axioms section_square_dvd_polar
#print axioms specialization_nullity_dvd

end ArkLib.ProximityGap.Frontier.OrdinaryPolarRankLoss
