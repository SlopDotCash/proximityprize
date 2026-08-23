/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSInterpolantZDegree
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSCurveTuple

/-!
# Issue #304, leg 3 — the Z-degree budget for the `L`-ary curve-fold GS interpolant

`GSInterpolantZDegree.lean` produced the integer GS interpolant with an explicit Z-degree
budget for the PAIR generic fold `f₀ + Z·f₁`; the `L`-ary curve cell production
(`exists_curve_cell_production_total`) was left **parametrized** on a degenerate-set budget
because the `L`-ary analogue was not in tree.  This file closes that gap by the identical
Cramer route — the only fold-specific ingredients are the matrix entries and their degree
bound:

* `gsMatrixZCurve` — the GS constraint system for the curve fold `∑ⱼ Zʲ·uⱼ` as an
  `F[Z]`-matrix; entry `(i,(s,t)),(a,b) ↦ C(a,s)·C(b,t)·ωᵢ^(a−s)·(∑ⱼ Zʲ·uⱼᵢ)^(b−t)`;
* `curvePolyZ_natDegree_le` / `gsMatrixZCurve_natDegree_le` — entry degrees are
  `≤ D·(L−1)` (the fold polynomial has Z-degree `≤ L−1`);
* `constraintMapCurve_eq_mulVec` — the matrix represents `constraintMap` for the curve
  fold over `K = F(Z)`;
* **`gs_existence_curve_zDegree`** — the headline: a nonzero integer interpolant
  `Q₀ ∈ F[Z][X][Y]` satisfying the GS `Conditions` for the curve fold, with every
  `F[Z]`-coefficient of `natDegree ≤ n·|constraintIndices m|·(D·(L−1))`;
* `gs_existence_curve_zDegree_card` — the `hbadz` producer: the degenerate set
  `{z : Q₀|_{Z:=z} = 0}` has size at most that budget — exactly the budget input of
  `exists_curve_cell_production_total`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

namespace GuruswamiSudan.OverRatFunc.ZDegree

open Polynomial Polynomial.Bivariate Finset GuruswamiSudan

variable {F : Type} [Field F]

attribute [local instance] Classical.propDecidable

local notation "K" => RatFunc F

/-- The curve fold's integer representative `∑ⱼ Zʲ·C(cⱼ)` has Z-degree `≤ L − 1`. -/
theorem curvePolyZ_natDegree_le {L : ℕ} (c : Fin L → F) :
    (∑ j : Fin L, (X : F[X]) ^ (j : ℕ) * C (c j)).natDegree ≤ L - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro j _
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hj := j.isLt
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
  omega

/-- The `L`-ary curve-fold Guruswami–Sudan constraint system as a matrix over `F[Z]`
(the inner `F[X]` is the polynomial ring in `Z`).  Row index: interpolation point × Hasse
order; column index: weighted-degree-bounded monomial. -/
noncomputable def gsMatrixZCurve (k n m L : ℕ) (ωs : Fin n ↪ F) (u : Fin L → Fin n → F)
    (D : ℕ) :
    Matrix (Fin n × constraintIndices m) (weigthBoundIndices k D) F[X] :=
  fun ist p =>
    C ((p.1.1.choose ist.2.1.1 : F) * (ωs ist.1) ^ (p.1.1 - ist.2.1.1) *
        (p.1.2.choose ist.2.1.2 : F)) *
      (∑ j : Fin L, (X : F[X]) ^ (j : ℕ) * C (u j ist.1)) ^ (p.1.2 - ist.2.1.2)

/-- Entry degrees of the curve constraint matrix are bounded by `D·(L−1)` (for `1 < k`):
the Z-degree of an entry is at most `(b − t)·(L−1) ≤ D·(L−1)`. -/
theorem gsMatrixZCurve_natDegree_le {k n m L : ℕ} (hk : 1 < k) (ωs : Fin n ↪ F)
    (u : Fin L → Fin n → F) (D : ℕ) (ist : Fin n × constraintIndices m)
    (p : weigthBoundIndices k D) :
    (gsMatrixZCurve k n m L ωs u D ist p).natDegree ≤ D * (L - 1) := by
  have hb : p.1.2 ≤ D := by
    have hp := p.2
    simp only [weigthBoundIndices, mem_filter] at hp
    have h1 : 1 ≤ k - 1 := by omega
    nlinarith [hp.2, p.1.1.zero_le]
  calc (gsMatrixZCurve k n m L ωs u D ist p).natDegree
      ≤ (C ((p.1.1.choose ist.2.1.1 : F) * (ωs ist.1) ^ (p.1.1 - ist.2.1.1) *
            (p.1.2.choose ist.2.1.2 : F))).natDegree +
        ((∑ j : Fin L, (X : F[X]) ^ (j : ℕ) * C (u j ist.1)) ^
          (p.1.2 - ist.2.1.2)).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 0 + (p.1.2 - ist.2.1.2) * (L - 1) := by
        gcongr
        · exact le_of_eq (Polynomial.natDegree_C _)
        · refine Polynomial.natDegree_pow_le.trans ?_
          gcongr
          exact curvePolyZ_natDegree_le _
    _ ≤ D * (L - 1) := by
        rw [zero_add]
        exact Nat.mul_le_mul_right _ (le_trans (Nat.sub_le _ _) hb)

/-- The matrix `gsMatrixZCurve`, mapped into `K = F(Z)`, represents `constraintMap` for
the curve fold on the monomial-coefficient coordinates. -/
theorem constraintMapCurve_eq_mulVec {k n m L : ℕ} (ωs : Fin n ↪ F)
    (u : Fin L → Fin n → F) (D : ℕ)
    (c : weigthBoundIndices k D → K) (ist : Fin n × constraintIndices m) :
    constraintMap k n m (liftedDomain ωs) (curveFold u) D c ist.1 ist.2 =
      ((gsMatrixZCurve k n m L ωs u D).map (algebraMap F[X] K)).mulVec c ist := by
  classical
  simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk, coeffsToPoly_eq_sum,
    map_sum, map_smul]
  rw [Matrix.mulVec]
  simp only [Matrix.map_apply, gsMatrixZCurve]
  congr 1
  ext p
  rw [evalConstraint_monomial]
  have hx : (liftedDomain ωs ist.1 : K) = algebraMap F[X] K (C (ωs ist.1)) := by
    simp only [liftedDomain, Function.Embedding.trans_apply, coeFieldEmb_apply]
    rw [IsScalarTower.algebraMap_apply F F[X] K, Polynomial.algebraMap_eq]
  have hy : curveFold u ist.1 =
      algebraMap F[X] K (∑ j : Fin L, (X : F[X]) ^ (j : ℕ) * C (u j ist.1)) := by
    rw [map_sum]
    simp only [curveFold]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, IsScalarTower.algebraMap_apply F F[X] K (u j ist.1),
      Polynomial.algebraMap_eq, RatFunc.algebraMap_X]
  rw [hx, hy]
  simp only [map_mul, map_pow, map_natCast, smul_eq_mul]
  ring

/-- **The `L`-ary curve interpolant with an explicit Z-degree budget (#304, leg 3).**

For the curve fold `∑ⱼ Zʲ·uⱼ` with `1 < k`, `n ≠ 0`, `1 ≤ m`, there is a *nonzero
integer* interpolant `Q₀ ∈ F[Z][X][Y]` whose image over `K = F(Z)` satisfies the
Guruswami–Sudan `Conditions` at the `gs_degree_bound`, and whose every
`F[Z]`-coefficient has `natDegree ≤ n·|constraintIndices m|·(gs_degree_bound·(L−1))`. -/
theorem gs_existence_curve_zDegree {n L : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (u : Fin L → Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (curveFold u)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      Q₀.natDegree ≤ gs_degree_bound k n m ∧
      ∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤
        (n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1)) := by
  classical
  set D := gs_degree_bound k n m with hD
  -- 1. nonzero kernel vector over K from the in-tree dimension count
  have hcount := gs_numVars_gt_numConstraints_of_gt_one hn hk hm
  obtain ⟨c, hc0, hck⟩ := exists_nonzero_solution_gen (F := K) k n m
    (liftedDomain ωs) (curveFold u) D hcount
  -- 2. it is a kernel vector of the mapped matrix
  have hker : ((gsMatrixZCurve k n m L ωs u D).map (algebraMap F[X] K)).mulVec c = 0 := by
    funext ist
    rw [← constraintMapCurve_eq_mulVec]
    have := congr_fun (congr_fun hck ist.1) ist.2
    simpa using this
  -- 3. Cramer: a polynomial kernel vector with the degree budget
  obtain ⟨c', hc'0, hc'ker, hdeg⟩ :=
    Matrix.exists_natDegree_le_kernel_vector_of_ratFunc
      (gsMatrixZCurve k n m L ωs u D)
      (fun i j => gsMatrixZCurve_natDegree_le hk ωs u D i j) c hc0 hker
  -- 4. the integer interpolant and its coefficient extraction
  set Q₀ : (F[X])[X][Y] := ∑ p : weigthBoundIndices k D,
      Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p)) with hQ₀
  have hcoeff : ∀ a b : ℕ, ((Q₀.coeff b).coeff a) =
      if h : (a, b) ∈ weigthBoundIndices k D then c' ⟨(a, b), h⟩ else 0 := by
    intro a b
    rw [hQ₀, Polynomial.finset_sum_coeff]
    have hterm : ∀ p : weigthBoundIndices k D,
        ((Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p))).coeff b).coeff a =
          if p.1 = (a, b) then c' p else 0 := by
      intro p
      rw [Polynomial.coeff_monomial]
      by_cases h2 : p.1.2 = b
      · rw [if_pos h2, Polynomial.coeff_monomial]
        by_cases h1 : p.1.1 = a
        · rw [if_pos h1, if_pos (Prod.ext h1 h2)]
        · rw [if_neg h1, if_neg (fun h => h1 (by rw [h]))]
      · rw [if_neg h2, Polynomial.coeff_zero, if_neg (fun h => h2 (by rw [h]))]
    calc (∑ p : weigthBoundIndices k D,
            ((Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p))).coeff b)).coeff a
        = ∑ p : weigthBoundIndices k D,
            ((Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p))).coeff b).coeff a := by
          rw [Polynomial.finset_sum_coeff]
      _ = ∑ p : weigthBoundIndices k D, if p.1 = (a, b) then c' p else 0 := by
          exact Finset.sum_congr rfl fun p _ => hterm p
      _ = if h : (a, b) ∈ weigthBoundIndices k D then c' ⟨(a, b), h⟩ else 0 := by
          by_cases h : (a, b) ∈ weigthBoundIndices k D
          · rw [dif_pos h, Finset.sum_eq_single (⟨(a, b), h⟩ : weigthBoundIndices k D)]
            · rw [if_pos rfl]
            · intro p _ hne
              rw [if_neg (fun hp => hne (Subtype.ext hp))]
            · intro habs; exact absurd (Finset.mem_univ _) habs
          · rw [dif_neg h, Finset.sum_eq_zero]
            intro p _
            rw [if_neg (fun hp => h (by rw [← hp]; exact p.2))]
  -- the mapped interpolant is `coeffsToPoly` of the mapped kernel vector
  set c'' : weigthBoundIndices k D → K := fun p => algebraMap F[X] K (c' p) with hc''
  have hmap : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K)) = coeffsToPoly k D c'' := by
    rw [coeffsToPoly_eq_sum, hQ₀, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Polynomial.map_monomial]
    simp only [Polynomial.mapRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Polynomial.map_monomial]
    rw [GuruswamiSudan.monomial, Polynomial.smul_monomial, Polynomial.smul_monomial,
      smul_eq_mul, mul_one]
  -- the mapped kernel vector is nonzero and in the kernel of `constraintMap`
  have hc''0 : c'' ≠ 0 := by
    intro habs
    apply hc'0
    funext p
    have := congr_fun habs p
    simpa [hc''] using (IsFractionRing.injective F[X] K)
      (by simpa [hc''] using congr_fun habs p)
  have hck'' : constraintMap k n m (liftedDomain ωs) (curveFold u) D c'' = 0 := by
    funext i st
    have hrep := constraintMapCurve_eq_mulVec (k := k) (m := m) ωs u D c'' (i, st)
    rw [show constraintMap k n m (liftedDomain ωs) (curveFold u) D c'' i st =
        constraintMap k n m (liftedDomain ωs) (curveFold u) D c''
          ((i, st) : Fin n × constraintIndices m).1 ((i, st) : Fin n × constraintIndices m).2
      from rfl, hrep]
    show (((gsMatrixZCurve k n m L ωs u D).map (algebraMap F[X] K)).mulVec c'') (i, st) = 0
    have : ((gsMatrixZCurve k n m L ωs u D).map (algebraMap F[X] K)).mulVec c'' (i, st) =
        algebraMap F[X] K ((gsMatrixZCurve k n m L ωs u D).mulVec c' (i, st)) := by
      simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, hc'', map_sum, map_mul]
    rw [this, hc'ker]
    simp
  -- injectivity of `coeffsToPoly` over K (for the nonzero leg)
  have h_inj : Function.Injective (coeffsToPoly (F := K) k D) := by
    have : Function.Injective (Finsupp.linearCombination K
        (fun p : weigthBoundIndices k D ↦ GuruswamiSudan.monomial (F := K) p.1.1 p.1.2)) :=
      linearIndependent_monomials.comp _ (fun p q h ↦ by aesop)
    exact this.comp (LinearEquiv.injective _)
  have hYdeg : Q₀.natDegree ≤ D := by
    rw [hQ₀]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro p _
    refine (Polynomial.natDegree_monomial_le _).trans ?_
    have hp := p.2
    simp only [weigthBoundIndices, mem_filter] at hp
    have h1 : 1 ≤ k - 1 := by omega
    nlinarith [hp.2, p.1.1.zero_le]
  refine ⟨Q₀, ?_, ?_, hYdeg, ?_⟩
  · -- Q₀ ≠ 0 via coefficient extraction
    obtain ⟨p₀, hp₀⟩ := Function.ne_iff.mp hc'0
    intro habs
    apply hp₀
    have := hcoeff p₀.1.1 p₀.1.2
    rw [habs] at this
    simp only [Polynomial.coeff_zero] at this
    rw [dif_pos (by exact (Prod.mk.eta (p := p₀.1)) ▸ p₀.2)] at this
    rw [show (⟨(p₀.1.1, p₀.1.2), _⟩ : weigthBoundIndices k D) = p₀ from
      Subtype.ext (Prod.mk.eta)] at this
    exact this.symm
  · -- Conditions: the four legs at K, mirroring the pair case with kernel vector c''
    rw [hmap]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun h ↦ hc''0 <| h_inj <| by simpa using h
    · convert Option.some_le_some.mpr (natWeightedDegree_coeffsToPoly_le k D c'') using 1
      exact weightedDegree_eq_natWeightedDegree
    · intro i
      exact eval_eq_zero_of_constraint_zero hm fun s t hst ↦ by
        simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk] at hck''
        have := congr_fun (congr_fun hck'' i) ⟨(s, t), Finset.mem_filter.2
          ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
            Finset.mem_range.mpr (by linarith)⟩, by linarith⟩⟩
        aesop
    · intro i
      apply rootMultiplicity_ge_of_shift_zero
      · exact fun h ↦ hc''0 <| h_inj <| by simpa using h
      · intro s t hst
        simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk] at hck''
        have := congr_fun (congr_fun hck'' i) ⟨(s, t), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
            Finset.mem_range.mpr (by linarith)⟩, by linarith⟩⟩
        aesop
  · -- the Z-degree budget
    intro b a
    rw [hcoeff a b]
    by_cases h : (a, b) ∈ weigthBoundIndices k D
    · rw [dif_pos h]
      refine (hdeg ⟨(a, b), h⟩).trans ?_
      have hcard : Fintype.card (Fin n × constraintIndices m) =
          n * (constraintIndices m).card := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
      rw [hcard]
    · rw [dif_neg h]
      simp

/-- **The `hbadz` producer for the curve cell production (#304, leg 3 closed).**  The
integer curve interpolant of `gs_existence_curve_zDegree` has a degenerate set of
cardinality at most the explicit Z-degree budget
`n·|constraintIndices m|·(gs_degree_bound·(L−1))` — exactly the budget input that
`exists_curve_cell_production_total` was parametrized on. -/
theorem gs_existence_curve_zDegree_card [Fintype F] {n L : ℕ} (k m : ℕ)
    (ωs : Fin n ↪ F) (u : Fin L → Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (curveFold u)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      Q₀.natDegree ≤ gs_degree_bound k n m ∧
      (Finset.univ.filter (fun z : F =>
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0)).card ≤
        (n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1)) := by
  obtain ⟨Q₀, h0, hcond, hY, hdeg⟩ := gs_existence_curve_zDegree k m ωs u hk hn hm
  exact ⟨Q₀, h0, hcond, hY, card_specialization_collapse_le h0 hdeg⟩

/-- **The subset-form budget producer** (decidability-free packaging of
`gs_existence_curve_zDegree_card`): any set of scalars collapsing the interpolant is
bounded by the explicit budget — the exact `hbadz` input shape of
`exists_curve_cell_production_total`, with no `Finset.filter` in the statement. -/
theorem gs_existence_curve_zDegree_badz [Fintype F] {n L : ℕ} (k m : ℕ)
    (ωs : Fin n ↪ F) (u : Fin L → Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (curveFold u)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      Q₀.natDegree ≤ gs_degree_bound k n m ∧
      ∀ S : Finset F,
        (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
        S.card ≤ (n * (constraintIndices m).card) * (gs_degree_bound k n m * (L - 1)) := by
  obtain ⟨Q₀, h0, hcond, hY, hcard⟩ := gs_existence_curve_zDegree_card k m ωs u hk hn hm
  refine ⟨Q₀, h0, hcond, hY, ?_⟩
  intro S hS
  refine le_trans (Finset.card_le_card ?_) hcard
  intro z hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS z hz⟩

end GuruswamiSudan.OverRatFunc.ZDegree

-- Axiom audit anchors: every result is axiom-clean `[propext, Classical.choice, Quot.sound]`.
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.curvePolyZ_natDegree_le
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.gsMatrixZCurve_natDegree_le
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.constraintMapCurve_eq_mulVec
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_curve_zDegree
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_curve_zDegree_card
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_curve_zDegree_badz
