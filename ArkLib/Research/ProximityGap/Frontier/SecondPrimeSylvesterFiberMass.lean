/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.Polynomial.ResultantDegree
import ArkLib.Data.Polynomial.FractionFieldResultant
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! # Root multiplicity of determinants under scalar specialization -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeSylvesterFiberMass

open Polynomial Finset Matrix Module
open scoped Polynomial

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

private theorem det_columns (A : Matrix ι ι K[X]) (z : K) (S : Finset ι)
    (h : ∀ j ∈ S, ∀ i, (A i j).eval z = 0) :
    (X - C z) ^ S.card ∣ A.det := by
  classical
  let v : ι → K[X] := fun j => if j ∈ S then X - C z else 1
  have hd (i j) : v j ∣ A i j := by
    by_cases hj : j ∈ S
    · simpa [v, hj, dvd_iff_isRoot] using h j hj i
    · simp [v, hj]
  choose B hB using hd
  have he : A = Matrix.of (fun i j => v j * B i j) := Matrix.ext hB
  rw [he]
  change _ ∣ (Matrix.of (fun i j => v j * (Matrix.of B) i j)).det
  rw [Matrix.det_mul_row]
  have hv : ∏ j, v j = (X - C z) ^ S.card := by simp [v]
  rw [hv]
  exact dvd_mul_right _ _

/-- A subspace annihilated by the evaluated matrix contributes its dimension to the
multiplicity of the determinant at that scalar. -/
theorem pow_dvd_det_of_subspace (A : Matrix ι ι K[X]) (z : K)
    (p : Submodule K (ι → K))
    (hp : ∀ x ∈ p, ((evalRingHom z).mapMatrix A).mulVec x = 0) :
    (X - C z) ^ finrank K p ∣ A.det := by
  classical
  obtain ⟨q, hq⟩ := p.exists_isCompl
  let b := ((Module.finBasis K p).prod (Module.finBasis K q)).map (p.prodEquivOfIsCompl q hq)
  let std := Pi.basisFun K ι
  let e := b.indexEquiv std
  let c := b.reindex e
  let P := std.toMatrix c
  let S := (univ : Finset (Fin (finrank K p))).map
    ((Function.Embedding.inl : Fin (finrank K p) ↪ _).trans e.toEmbedding)
  have hS : S.card = finrank K p := by simp [S]
  let D := A * C.mapMatrix P
  have hzero (j) (hj : j ∈ S) (i) : (D i j).eval z = 0 := by
    obtain ⟨u, _, rfl⟩ := mem_map.mp hj
    have hx : b (Sum.inl u) ∈ p := by simp [b, Submodule.coe_prodEquivOfIsCompl']
    have hxu := congrFun (hp _ hx) i
    simpa [D, P, c, std, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Module.Basis.toMatrix_apply, eval_finsetSum, eval_mul] using hxu
  have hdiv := det_columns D z S hzero
  rw [hS] at hdiv
  have hi := std.toMatrix_mul_toMatrix_flip c
  have hP : IsUnit P.det := isUnit_iff_ne_zero.mpr (Matrix.det_ne_zero_of_right_inverse hi)
  have hiP : IsUnit (C.mapMatrix P).det := by rw [← RingHom.map_det]; exact hP.map C
  exact hiP.dvd_mul_right.mp (by simpa [D, Matrix.det_mul] using hdiv)

private noncomputable def mulLT (f : K[X]) {l m : ℕ} (hm : f.natDegree + l ≤ m) :
    degreeLT K l →ₗ[K] degreeLT K m where
  toFun u := ⟨f * u.val, by
    by_cases hu : u.val = 0
    · simp [hu]
    apply mem_degreeLT.mpr
    by_cases hf : f = 0
    · simp [hf]
    apply (natDegree_lt_iff_degree_lt (mul_ne_zero hf hu)).mp
    rw [natDegree_mul hf hu]
    have := (natDegree_lt_iff_degree_lt hu).mpr (mem_degreeLT.mp u.property)
    omega⟩
  map_add' u v := Subtype.ext (mul_add _ _ _)
  map_smul' a u := Subtype.ext (mul_smul_comm _ _ _)

/-- A common factor of degree `l` in a scalar fiber forces the `l`th power of the
scalar's linear factor to divide the resultant. The two cofactors give an injective
space of polynomial syzygies. -/
theorem pow_dvd_resultant (F G : K[X][X]) (z : K) {m n l : ℕ}
    (T U V : K[X]) (hU : U ≠ 0)
    (hf : F.map (evalRingHom z) = T * U) (hg : G.map (evalRingHom z) = T * V)
    (hm : U.natDegree + l ≤ m) (hn : V.natDegree + l ≤ n)
    (ht : T.natDegree ≤ l) : (X - C z) ^ l ∣ F.resultant G m n := by
  classical
  let f := F.map (evalRingHom z)
  let g := G.map (evalRingHom z)
  have hf' : f.natDegree ≤ m := by
    dsimp [f]; rw [hf]; exact natDegree_mul_le.trans (by omega)
  have hg' : g.natDegree ≤ n := by
    dsimp [g]; rw [hg]; exact natDegree_mul_le.trans (by omega)
  let b := ((degreeLT.basis K m).prod (degreeLT.basis K n)).reindex finSumFinEquiv
  let c := degreeLT.basis K (m + n)
  let L := b.equivFun.toLinearMap.comp ((mulLT U hm).prod (-(mulLT V hn)))
  have hi : Function.Injective L := by
    intro u v huv
    have hh := congrArg Prod.fst (b.equivFun.injective huv)
    exact Subtype.ext (mul_left_cancel₀ hU (congrArg Subtype.val hh))
  have hzero (v) (hv : v ∈ LinearMap.range L) :
      ((evalRingHom z).mapMatrix (F.sylvester G m n)).mulVec v = 0 := by
    obtain ⟨u, rfl⟩ := hv
    rw [← sylvester_map_map, ← toMatrix_sylvesterMap' _ _ hf' hg']
    change ((sylvesterMap f g hf' hg').toMatrix b c).mulVec (b.repr _) = _
    rw [LinearMap.toMatrix_mulVec_repr]
    suffices h : sylvesterMap f g hf' hg' (((mulLT U hm).prod (-(mulLT V hn))) u) = 0 by
      rw [h, map_zero]
      rfl
    apply Subtype.ext
    change f * (-(V * u.val)) + g * (U * u.val) = 0
    change F.map _ * (-(V * u.val)) + G.map _ * (U * u.val) = 0
    rw [hf, hg]
    ring
  have hd := pow_dvd_det_of_subspace (F.sylvester G m n) z (LinearMap.range L) hzero
  rwa [LinearMap.finrank_range_of_inj hi, Module.finrank_eq_card_basis (degreeLT.basis K l),
    Fintype.card_fin] at hd

/-- A nonzero polynomial has enough degree to pay for the multiplicities of all
members of an arbitrary finite set of distinct scalars. -/
theorem fiber_mass_le {P : K[X]} (hP : P ≠ 0) (S : Finset K) (l : ℕ)
    (h : ∀ z ∈ S, (X - C z) ^ l ∣ P) : S.card * l ≤ P.natDegree := by
  classical
  have hs : ∑ z ∈ S, P.roots.count z ≤ P.roots.card := by
    let T := S ∪ P.roots.toFinset
    have hsub : S ⊆ T := subset_union_left
    refine (sum_le_sum_of_subset_of_nonneg hsub (by intros; omega)).trans_eq ?_
    exact Multiset.sum_count_eq_card (fun z hz => mem_union_right _ (Multiset.mem_toFinset.mpr hz))
  have hm := sum_le_sum (s := S) (fun z hz =>
    show l ≤ P.roots.count z from by
      rw [count_roots]; exact (le_rootMultiplicity_iff hP).mpr (h z hz))
  exact (by simpa using hm : S.card * l ≤ _).trans (hs.trans P.card_roots')

/-- A degree-preserving scalar specialization which is a square up to scalar forces
half its coordinate degree as a multiplicity in the derivative resultant. -/
theorem square_fiber_dvd (H : K[X][X]) (z c : K) (T : K[X]) (hc : c ≠ 0)
    (hr : 0 < H.natDegree)
    (hdeg : (H.map (evalRingHom z)).natDegree = H.natDegree)
    (hsq : H.map (evalRingHom z) = C c * T ^ 2) :
    H.natDegree = 2 * T.natDegree ∧
      (X - C z) ^ T.natDegree ∣
        H.resultant H.derivative H.natDegree (H.natDegree - 1) := by
  have hd : H.natDegree = 2 * T.natDegree := by
    rw [← hdeg, hsq, natDegree_C_mul hc, natDegree_pow]
  have hT : T ≠ 0 := by intro he; simp [he] at hd; omega
  refine ⟨hd, pow_dvd_resultant H H.derivative z T (C c * T)
    (C (2 * c) * T.derivative) (mul_ne_zero (C_ne_zero.mpr hc) hT) ?_ ?_ ?_ ?_ le_rfl⟩
  · rw [hsq]; ring
  · rw [← derivative_map, hsq, derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_pow]
    simp
    ring
  · rw [natDegree_C_mul hc]; omega
  · have hh := natDegree_C_mul_le (2 * c) T.derivative
    have ht := natDegree_derivative_le T
    omega

/-- A generically separable bivariate polynomial of positive coordinate degree has
at most four times its scalar degree distinct, degree-preserving square fibers.
Scalar multiples of squares are included, over any field. -/
theorem square_fiber_count (H : K[X][X]) (hr : 0 < H.natDegree)
    (hsep : (H.map (algebraMap K[X] (FractionRing K[X]))).Separable)
    (S : Finset K)
    (hS : ∀ z ∈ S, (H.map (evalRingHom z)).natDegree = H.natDegree ∧
      ∃ c : K, ∃ T : K[X], c ≠ 0 ∧ H.map (evalRingHom z) = C c * T ^ 2) :
    S.card ≤ 4 * Bivariate.degreeX H := by
  classical
  obtain h0 | ⟨z, hz⟩ := S.eq_empty_or_nonempty
  · simp [h0]
  obtain ⟨hd, c, T, hc, he⟩ := hS z hz
  obtain ⟨hdeg, _⟩ := square_fiber_dvd H z c T hc hr hd he
  let R := H.resultant H.derivative H.natDegree (H.natDegree - 1)
  have hR : R ≠ 0 := resultant_derivative_ne_zero_of_separable_map_fractionField H hsep
  have hmass := fiber_mass_le hR S T.natDegree (fun w hw => by
    obtain ⟨hwdeg, e, U, heu, hwu⟩ := hS w hw
    obtain ⟨hu, hdiv⟩ := square_fiber_dvd H w e U heu hr hwdeg hwu
    rwa [show T.natDegree = U.natDegree by omega])
  have hb := natDegree_resultant_derivative_padded_le H
  change R.natDegree ≤ _ at hb
  have hr' : 0 < T.natDegree := by omega
  apply Nat.le_of_mul_le_mul_right _ hr'
  calc
    S.card * T.natDegree ≤ R.natDegree := hmass
    _ ≤ (2 * H.natDegree - 1) * Bivariate.degreeX H := hb
    _ ≤ (2 * H.natDegree) * Bivariate.degreeX H := by gcongr; omega
    _ = 4 * Bivariate.degreeX H * T.natDegree := by rw [hdeg]; ring

open scoped Classical in
private theorem vanishing_count {R : Type*} [CommRing R] [IsDomain R]
    (φ : K →+* R) (M : Finset K) (P : R[X]) (hp : P ≠ 0) :
    (M.filter fun z => P.eval (φ z) = 0).card ≤ P.natDegree := by
  classical
  by_contra! h
  apply hp
  let S := M.filter fun z => P.eval (φ z) = 0
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := fun z : S => φ (z : K))
    (φ.injective.comp Subtype.val_injective)
  · exact fun z => (mem_filter.mp z.property).2
  · simpa only [Fintype.card_coe] using h

/-- Count all square fibers after removing scalar- and bivariate-factor zero specializations.
Dropping coordinate degree is charged against the scalar degree of the leading coefficient. -/
theorem exceptional_square_fiber_count (s : K[X]) (V H : K[X][X]) (M : Finset K)
    (hs : s ≠ 0) (hV : V ≠ 0) (hr : 0 < (Bivariate.swap H).natDegree)
    (hsep : ((Bivariate.swap H).map (algebraMap K[X] (FractionRing K[X]))).Separable)
    (hM : ∀ z ∈ M, s.eval z ≠ 0 → V.eval (C z) ≠ 0 → IsSquare (H.eval (C z))) :
    M.card ≤ s.natDegree + V.natDegree + 5 * H.natDegree := by
  classical
  let G := Bivariate.swap H
  let E := M.filter fun z => s.eval z = 0
  let D := M.filter fun z => V.eval (C z) = 0
  let L := M.filter fun z => G.leadingCoeff.eval z = 0
  let S := M \ ((E ∪ D) ∪ L)
  have hE : E.card ≤ s.natDegree := vanishing_count (RingHom.id K) M s hs
  have hD : D.card ≤ V.natDegree := by
    convert vanishing_count (K := K) (C : K →+* K[X]) M V hV using 1
    congr 1
    ext z
    simp [D]
  have hn : G ≠ 0 := fun he => by simp [show Bivariate.swap H = 0 from he] at hr
  have hL : L.card ≤ H.natDegree := calc
    L.card ≤ G.leadingCoeff.natDegree :=
      vanishing_count (RingHom.id K) M G.leadingCoeff (leadingCoeff_ne_zero.mpr hn)
    _ ≤ Bivariate.degreeX G := Bivariate.coeff_natDegree_le_degreeX G G.natDegree
    _ = H.natDegree := Bivariate.degreeX_swap H
  have hS : S.card ≤ 4 * H.natDegree := by
    rw [← show Bivariate.degreeX G = H.natDegree from Bivariate.degreeX_swap H]
    apply square_fiber_count G hr hsep S
    intro z hz
    obtain ⟨hm, hcut⟩ := mem_sdiff.mp hz
    have he : s.eval z ≠ 0 := fun hh =>
      hcut (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hm, hh⟩)))
    have hd : V.eval (C z) ≠ 0 := fun hh =>
      hcut (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hm, hh⟩)))
    have hl : G.leadingCoeff.eval z ≠ 0 := fun hh =>
      hcut (mem_union_right _ (mem_filter.mpr ⟨hm, hh⟩))
    refine ⟨natDegree_map_of_leadingCoeff_ne_zero _ hl, ?_⟩
    obtain ⟨T, hT⟩ := hM z hm he hd
    have hs' : H.eval (C z) = G.map (evalRingHom z) := by
      simpa only [Bivariate.evalY, Bivariate.evalX_eq_map, G] using
        Bivariate.evalY_eq_evalX_swap z H
    refine ⟨1, T, one_ne_zero, ?_⟩
    simpa only [map_one, one_mul, pow_two, ← hs'] using hT
  have hsplit := card_le_card_sdiff_add_card (s := M) (t := (E ∪ D) ∪ L)
  have hh := card_union_le (E ∪ D) L
  have hhd := card_union_le E D
  change M.card ≤ S.card + _ at hsplit
  omega

end ArkLib.ProximityGap.Frontier.SecondPrimeSylvesterFiberMass
