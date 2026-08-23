/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.PolynomialMatrixKernel
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSOverRatFunc

/-!
# Issue #302, unit (2) closer — a Z-degree budget for the generic-fold GS interpolant

`GSIntegralFactorAssignment.lean` reduced unit (2) of the Hab25 ledger to exactly one
statement: an *integer* (i.e. `F[Z]`-coefficient) Guruswami–Sudan interpolant for the generic
fold `f₀ + Z·f₁` whose `Z`-degree is explicitly bounded — then the only degenerate scalars in
the whole #302 chain, `{z : Q₀|_{Z:=z} = 0}`, form a set of size `≤ deg_Z Q₀`.

This file produces that interpolant by the **Cramer route** designed on the issue:

* `gsMatrixZ` — the GS interpolation conditions for the generic fold as an `F[Z]`-matrix
  (rows = `n · |constraintIndices m|` Hasse constraints, columns = weighted-degree monomials),
  with entry `(i,(s,t)),(a,b) ↦ C(a,s)·C(b,t)·ωᵢ^(a-s) · (f₀ᵢ + Z·f₁ᵢ)^(b-t)`, entry degrees
  `≤ D` (`gsMatrixZ_natDegree_le`);
* `evalConstraint_monomial` — the binomial form of the Hasse constraint on a monomial, the
  bridge between `constraintMap` and the matrix (`constraintMap_eq_mulVec`);
* the in-tree `exists_nonzero_solution_gen` at `K = F(Z)` certifies a nonzero kernel vector
  over the fraction field, and `Matrix.exists_natDegree_le_kernel_vector_of_ratFunc`
  (the landed unit-(2) Cramer lemma) converts it to a nonzero *polynomial* kernel vector with
  entries of degree `≤ (n·|constraintIndices m|)·D`;
* **`gs_existence_over_ratfunc_zDegree`** — the headline: an integer interpolant
  `Q₀ : F[Z][X][Y]`, nonzero, whose `K`-image satisfies the GS `Conditions` for the generic
  fold at the `gs_degree_bound`, with every `F[Z]`-coefficient of `natDegree ≤`
  `n·|constraintIndices m|·gs_degree_bound k n m`.
-/

namespace GuruswamiSudan.OverRatFunc.ZDegree

open Polynomial Polynomial.Bivariate Finset GuruswamiSudan

variable {F : Type} [Field F]

attribute [local instance] Classical.propDecidable

local notation "K" => RatFunc F

/-- The `(s,t)` Hasse constraint of the monomial `X^a·Y^b` at `(x, y)`:
`shift (X^a Y^b) x y = C((X+Cx)^a) * (Y + C (C y))^b`, whose `(s,t)` coefficient is the
binomial product. Stated over an arbitrary field. -/
theorem evalConstraint_monomial {L : Type} [Field L] (x y : L) (s t a b : ℕ) :
    evalConstraint x y s t (GuruswamiSudan.monomial a b) =
      (a.choose s : L) * x ^ (a - s) * ((b.choose t : L) * y ^ (b - t)) := by
  classical
  have hshift : Bivariate.shift (GuruswamiSudan.monomial (F := L) a b) x y =
      C ((X + C x) ^ a) * (Y + C (C y)) ^ b := by
    simp only [GuruswamiSudan.monomial, Bivariate.shift]
    rw [Polynomial.monomial_comp]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, map_C]
    congr 1
    · rw [show (Polynomial.monomial a (1 : L)) = X ^ a from (Polynomial.X_pow_eq_monomial a).symm]
      simp [Polynomial.compRingHom]
    · simp [Polynomial.compRingHom]
  simp only [evalConstraint, LinearMap.coe_mk, AddHom.coe_mk, hshift]
  rw [Polynomial.coeff_C_mul]
  rw [Polynomial.coeff_X_add_C_pow]
  rw [show ((C y) ^ (b - t) * ((b.choose t : ℕ) : L[X])) =
      C (y ^ (b - t) * ((b.choose t : ℕ) : L)) by
    rw [← Polynomial.C_pow, ← Polynomial.C_eq_natCast, ← Polynomial.C_mul]]
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_X_add_C_pow]
  ring

/-- The generic-fold Guruswami–Sudan constraint system as a matrix over `F[Z]` (we use the
inner `F[X]` as the polynomial ring in `Z`). Row index: interpolation point × Hasse order;
column index: weighted-degree-bounded monomial. -/
noncomputable def gsMatrixZ (k n m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F) (D : ℕ) :
    Matrix (Fin n × constraintIndices m) (weigthBoundIndices k D) F[X] :=
  fun ist p =>
    C ((p.1.1.choose ist.2.1.1 : F) * (ωs ist.1) ^ (p.1.1 - ist.2.1.1) *
        (p.1.2.choose ist.2.1.2 : F)) *
      (C (f₀ ist.1) + X * C (f₁ ist.1)) ^ (p.1.2 - ist.2.1.2)

/-- Entry degrees of the constraint matrix are bounded by `D` (for `1 < k`): the `Z`-degree of
an entry is at most `b - t ≤ b ≤ D` since `a + (k-1)·b ≤ D` and `k - 1 ≥ 1`. -/
theorem gsMatrixZ_natDegree_le {k n m : ℕ} (hk : 1 < k) (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (D : ℕ) (ist : Fin n × constraintIndices m)
    (p : weigthBoundIndices k D) :
    (gsMatrixZ k n m ωs f₀ f₁ D ist p).natDegree ≤ D := by
  have hb : p.1.2 ≤ D := by
    have hp := p.2
    simp only [weigthBoundIndices, mem_filter] at hp
    have h1 : 1 ≤ k - 1 := by omega
    nlinarith [hp.2, p.1.1.zero_le]
  calc (gsMatrixZ k n m ωs f₀ f₁ D ist p).natDegree
      ≤ (C ((p.1.1.choose ist.2.1.1 : F) * (ωs ist.1) ^ (p.1.1 - ist.2.1.1) *
            (p.1.2.choose ist.2.1.2 : F))).natDegree +
        ((C (f₀ ist.1) + X * C (f₁ ist.1)) ^ (p.1.2 - ist.2.1.2)).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 0 + (p.1.2 - ist.2.1.2) * 1 := by
        gcongr
        · exact le_of_eq (Polynomial.natDegree_C _)
        · refine Polynomial.natDegree_pow_le.trans ?_
          gcongr
          refine (Polynomial.natDegree_add_le _ _).trans ?_
          refine max_le (by simp) ?_
          exact (Polynomial.natDegree_mul_le).trans (by simp [Polynomial.natDegree_C])
    _ ≤ D := by omega

/-- `coeffsToPoly` as a plain finite sum over the index set. -/
theorem coeffsToPoly_eq_sum {L : Type} [Field L] (k D : ℕ)
    (c : weigthBoundIndices k D → L) :
    coeffsToPoly k D c =
      ∑ p : weigthBoundIndices k D, c p • GuruswamiSudan.monomial p.1.1 p.1.2 := by
  classical
  simp only [coeffsToPoly, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  · rfl
  · intro p; exact zero_smul _ _

/-- The matrix `gsMatrixZ`, mapped into `K = F(Z)`, represents `constraintMap` for the
generic fold on the monomial-coefficient coordinates. -/
theorem constraintMap_eq_mulVec {k n m : ℕ} (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F) (D : ℕ)
    (c : weigthBoundIndices k D → K) (ist : Fin n × constraintIndices m) :
    constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c ist.1 ist.2 =
      ((gsMatrixZ k n m ωs f₀ f₁ D).map (algebraMap F[X] K)).mulVec c ist := by
  classical
  simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk, coeffsToPoly_eq_sum,
    map_sum, map_smul]
  rw [Matrix.mulVec]
  simp only [Matrix.map_apply, gsMatrixZ]
  congr 1
  ext p
  rw [evalConstraint_monomial]
  have hx : (liftedDomain ωs ist.1 : K) = algebraMap F[X] K (C (ωs ist.1)) := by
    simp only [liftedDomain, Function.Embedding.trans_apply, coeFieldEmb_apply]
    rw [IsScalarTower.algebraMap_apply F F[X] K, Polynomial.algebraMap_eq]
  have hy : genericFold f₀ f₁ ist.1 =
      algebraMap F[X] K (C (f₀ ist.1) + X * C (f₁ ist.1)) := by
    simp only [genericFold, map_add, map_mul]
    rw [IsScalarTower.algebraMap_apply F F[X] K, IsScalarTower.algebraMap_apply F F[X] K,
      Polynomial.algebraMap_eq, RatFunc.algebraMap_X]
  rw [hx, hy]
  simp only [map_mul, map_pow, map_natCast, smul_eq_mul]
  ring

/-- **The unit-(2) closer (#302): integer GS interpolant with an explicit Z-degree budget.**

For the generic fold `f₀ + Z·f₁` with `1 < k`, `n ≠ 0`, `1 ≤ m`, there is a *nonzero integer*
interpolant `Q₀ ∈ F[Z][X][Y]` whose image over `K = F(Z)` satisfies the Guruswami–Sudan
`Conditions` at the `gs_degree_bound`, and whose every `F[Z]`-coefficient has
`natDegree ≤ n·|constraintIndices m|·gs_degree_bound k n m`. Consequently the degenerate set
`{z : Q₀|_{Z:=z} = 0}` of `GSIntegralFactorAssignment` has size at most that budget. -/
theorem gs_existence_over_ratfunc_zDegree {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (genericFold f₀ f₁)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      ∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤
        (n * (constraintIndices m).card) * gs_degree_bound k n m := by
  classical
  set D := gs_degree_bound k n m with hD
  -- 1. nonzero kernel vector over K from the in-tree dimension count
  have hcount := gs_numVars_gt_numConstraints_of_gt_one hn hk hm
  obtain ⟨c, hc0, hck⟩ := exists_nonzero_solution_gen (F := K) k n m
    (liftedDomain ωs) (genericFold f₀ f₁) D hcount
  -- 2. it is a kernel vector of the mapped matrix
  have hker : ((gsMatrixZ k n m ωs f₀ f₁ D).map (algebraMap F[X] K)).mulVec c = 0 := by
    funext ist
    rw [← constraintMap_eq_mulVec]
    have := congr_fun (congr_fun hck ist.1) ist.2
    simpa using this
  -- 3. Cramer: a polynomial kernel vector with the degree budget
  obtain ⟨c', hc'0, hc'ker, hdeg⟩ :=
    Matrix.exists_natDegree_le_kernel_vector_of_ratFunc
      (gsMatrixZ k n m ωs f₀ f₁ D)
      (fun i j => gsMatrixZ_natDegree_le hk ωs f₀ f₁ D i j) c hc0 hker
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
  have hck'' : constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c'' = 0 := by
    funext i st
    have hrep := constraintMap_eq_mulVec (k := k) (m := m) ωs f₀ f₁ D c'' (i, st)
    rw [show constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c'' i st =
        constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c''
          ((i, st) : Fin n × constraintIndices m).1 ((i, st) : Fin n × constraintIndices m).2
      from rfl, hrep]
    show (((gsMatrixZ k n m ωs f₀ f₁ D).map (algebraMap F[X] K)).mulVec c'') (i, st) = 0
    have : ((gsMatrixZ k n m ωs f₀ f₁ D).map (algebraMap F[X] K)).mulVec c'' (i, st) =
        algebraMap F[X] K ((gsMatrixZ k n m ωs f₀ f₁ D).mulVec c' (i, st)) := by
      simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, hc'', map_sum, map_mul]
    rw [this, hc'ker]
    simp
  -- injectivity of `coeffsToPoly` over K (for the nonzero leg)
  have h_inj : Function.Injective (coeffsToPoly (F := K) k D) := by
    have : Function.Injective (Finsupp.linearCombination K
        (fun p : weigthBoundIndices k D ↦ GuruswamiSudan.monomial (F := K) p.1.1 p.1.2)) :=
      linearIndependent_monomials.comp _ (fun p q h ↦ by aesop)
    exact this.comp (LinearEquiv.injective _)
  refine ⟨Q₀, ?_, ?_, ?_⟩
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
  · -- Conditions: the four legs at K, mirroring `gs_existence` with kernel vector c''
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

/-- **Quantitative collapse bound** (the roots-counting corollary). If every
`F[Z]`-coefficient of a nonzero `Q₀ : F[Z][X][Y]` has `natDegree ≤ B`, then the degenerate
set `{z : Q₀|_{Z:=z} = 0}` has at most `B` elements: any fixed nonzero coefficient of `Q₀`
vanishes at every such `z` (two levels of `Polynomial.coeff_map`), and a nonzero polynomial
of `natDegree ≤ B` has at most `B` roots. Quantitative companion of
`GuruswamiSudan.OverRatFunc.specialization_collapse_finite`. -/
theorem card_specialization_collapse_le [Fintype F] {Q₀ : (F[X])[X][Y]} (hQ₀ : Q₀ ≠ 0)
    {B : ℕ} (hdeg : ∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤ B) :
    (Finset.univ.filter (fun z : F =>
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0)).card ≤ B := by
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hQ₀
  have hi' : Q₀.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hi'
  have hj' : (Q₀.coeff i).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  refine (Polynomial.card_le_degree_of_subset_roots ?_).trans (hdeg i j)
  intro z hz
  rw [Finset.mem_val, Finset.mem_filter] at hz
  have h1 : ((Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).coeff i).coeff j
      = 0 := by
    rw [hz.2]
    simp
  rw [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
    Polynomial.coe_evalRingHom] at h1
  exact (Polynomial.mem_roots hj').mpr h1

/-- **The `hbadz` producer (#302, unit (2) endgame).** The integer GS interpolant of
`gs_existence_over_ratfunc_zDegree` has a degenerate set of cardinality at most the
explicit Z-degree budget `n·|constraintIndices m|·gs_degree_bound k n m` — exactly the
`hbadz` input consumed by `exists_cell_production` / `bad_card_le_of_cell_production` in
`GSCellProduction.lean`. -/
theorem gs_existence_over_ratfunc_zDegree_card [Fintype F] {n : ℕ} (k m : ℕ)
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (genericFold f₀ f₁)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      (Finset.univ.filter (fun z : F =>
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0)).card ≤
        n * (constraintIndices m).card * gs_degree_bound k n m := by
  obtain ⟨Q₀, h0, hcond, hdeg⟩ := gs_existence_over_ratfunc_zDegree k m ωs f₀ f₁ hk hn hm
  exact ⟨Q₀, h0, hcond, card_specialization_collapse_le h0 hdeg⟩

end GuruswamiSudan.OverRatFunc.ZDegree

-- Axiom audit anchors: every result is axiom-clean `[propext, Classical.choice, Quot.sound]`.
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.evalConstraint_monomial
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.gsMatrixZ_natDegree_le
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.coeffsToPoly_eq_sum
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.constraintMap_eq_mulVec
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_over_ratfunc_zDegree
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.card_specialization_collapse_le
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_over_ratfunc_zDegree_card
