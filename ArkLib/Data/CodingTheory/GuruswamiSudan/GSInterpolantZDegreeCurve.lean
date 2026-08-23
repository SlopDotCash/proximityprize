/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSInterpolantZDegreeGraded
import ArkLib.ToMathlib.CurveHenselSupply

/-!
# Issue #302 — the `L`-ary graded Z-degree GS interpolant (curve fold)

`GSInterpolantZDegreeGraded.lean` produced the integer Guruswami–Sudan interpolant for the
*pair* generic fold `f₀ + Z·f₁` with the linear-in-`n` Z-degree budget
`n·|constraintIndices m|·(gs_degree_bound k n m/(k-1))`, by solving the GS system gradedly
over `F` ([BCIKS20] §5.2.1 dimension count).  This file is the **`L`-ary curve-fold mirror**:
the `Y`-point is the integral curve point `intPointYCurve f i = ∑ⱼ Zʲ·C(fⱼ i)` of
`CurveHenselSupply.lean` (Z-degree `≤ L-1`) instead of the affine point `C f₀ᵢ + Z·C f₁ᵢ`
(Z-degree `≤ 1`), so

* the curve constraint matrix `gsMatrixZCurve` has column-wise entry Z-degree
  `≤ (L-1)·b` (`gsMatrixZCurve_natDegree_le_col`);
* the graded budgets pick up exactly one factor `L-1`: with `DY := gs_degree_bound k n m/(k-1)`
  the unknown blocks have size `DZ + 1` for `DZ := n·|constraintIndices m|·((L-1)·DY)` and the
  constraint blocks have size `DZ + (L-1)·DY + 1` — the *same* parametric dimension count
  `graded_count` applies with `DY := (L-1)·DY` substituted;
* the constraint correspondence `constraintMapCurve_eq_mulVec` runs through
  `map_intPointYCurve` in place of the affine `hy`-bridge; everything else transfers verbatim.

**Headline** (`gs_existence_zDegree_curve`): a nonzero integer interpolant `Q₀ : F[Z][X][Y]`
satisfying the GS `Conditions` for the `L`-ary curve fold over `K = F(Z)` whose every
`F[Z]`-coefficient has `natDegree` at most
`n·|constraintIndices m|·((L-1)·(gs_degree_bound k n m/(k-1)))`.
With `card_specialization_collapse_le` this is the `hbadz` producer
(`gs_existence_zDegree_curve_card`) consumed by `exists_curve_cell_production_total` in
`Hab25CurveCellProduction.lean`.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GuruswamiSudan.OverRatFunc.ZDegree.Curve

open Polynomial Polynomial.Bivariate Finset GuruswamiSudan
open GuruswamiSudan.OverRatFunc.ZDegree.Graded

variable {F : Type} [Field F]

attribute [local instance] Classical.propDecidable

local notation "K" => RatFunc F

/-- The integral curve `Y`-point `∑ⱼ Zʲ·C(fⱼ i)` has `Z`-degree at most `L - 1`. -/
theorem intPointYCurve_natDegree_le {n L : ℕ} (f : Fin L → Fin n → F) (i : Fin n) :
    (intPointYCurve f i).natDegree ≤ L - 1 := by
  rw [intPointYCurve]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 : (Polynomial.X ^ (j : ℕ) : F[X]).natDegree ≤ (j : ℕ) :=
    Polynomial.natDegree_X_pow_le _
  have h2 : (Polynomial.C (f j i)).natDegree = 0 := Polynomial.natDegree_C _
  have hj := j.isLt
  omega

/-- The `L`-ary curve-fold Guruswami–Sudan constraint system as a matrix over `F[Z]` (the
inner `F[X]` is the polynomial ring in `Z`).  Row index: interpolation point × Hasse order;
column index: weighted-degree-bounded monomial.  Mirror of `gsMatrixZ` with the affine
`Y`-point replaced by the curve point `intPointYCurve f i`. -/
noncomputable def gsMatrixZCurve (k n m : ℕ) (ωs : Fin n ↪ F) {L : ℕ}
    (f : Fin L → Fin n → F) (D : ℕ) :
    Matrix (Fin n × constraintIndices m) (weigthBoundIndices k D) F[X] :=
  fun ist p =>
    C ((p.1.1.choose ist.2.1.1 : F) * (ωs ist.1) ^ (p.1.1 - ist.2.1.1) *
        (p.1.2.choose ist.2.1.2 : F)) *
      (intPointYCurve f ist.1) ^ (p.1.2 - ist.2.1.2)

/-- **Column-wise Z-degree bound** for `gsMatrixZCurve`: the entry in column `(a, b)` has
`natDegree ≤ (L-1)·b` — the entry is a constant times `(intPointYCurve f i)^(b-t)` and the
base has `Z`-degree `≤ L-1`.  The `L`-ary mirror of `gsMatrixZ_natDegree_le_col`. -/
theorem gsMatrixZCurve_natDegree_le_col {k n m L : ℕ} (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F) (D : ℕ) (ist : Fin n × constraintIndices m)
    (p : weigthBoundIndices k D) :
    (gsMatrixZCurve k n m ωs f D ist p).natDegree ≤ (L - 1) * p.1.2 := by
  calc (gsMatrixZCurve k n m ωs f D ist p).natDegree
      ≤ (C ((p.1.1.choose ist.2.1.1 : F) * (ωs ist.1) ^ (p.1.1 - ist.2.1.1) *
            (p.1.2.choose ist.2.1.2 : F))).natDegree +
        ((intPointYCurve f ist.1) ^ (p.1.2 - ist.2.1.2)).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 0 + (p.1.2 - ist.2.1.2) * (L - 1) := by
        gcongr
        · exact le_of_eq (Polynomial.natDegree_C _)
        · refine Polynomial.natDegree_pow_le.trans ?_
          gcongr
          exact intPointYCurve_natDegree_le f ist.1
    _ ≤ (L - 1) * p.1.2 := by
        rw [zero_add, Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- The matrix `gsMatrixZCurve`, mapped into `K = F(Z)`, represents `constraintMap` for the
`L`-ary curve fold on the monomial-coefficient coordinates — the curve mirror of
`constraintMap_eq_mulVec`, with the `hy`-bridge supplied by `map_intPointYCurve`. -/
theorem constraintMapCurve_eq_mulVec {k n m L : ℕ} (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F) (D : ℕ)
    (c : weigthBoundIndices k D → K) (ist : Fin n × constraintIndices m) :
    constraintMap k n m (liftedDomain ωs) (curveFold f) D c ist.1 ist.2 =
      ((gsMatrixZCurve k n m ωs f D).map (algebraMap F[X] K)).mulVec c ist := by
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
  have hy : curveFold f ist.1 = algebraMap F[X] K (intPointYCurve f ist.1) :=
    (map_intPointYCurve f ist.1).symm
  rw [hx, hy]
  simp only [map_mul, map_pow, map_natCast, smul_eq_mul]
  ring

/-- The graded GS system for the curve fold as an `F`-linear map: unknown blocks `x(p, ·)`
are sent to the `Z`-coefficients (orders `0..DW`) of every `F[Z]`-valued Hasse constraint of
the `L`-ary curve fold.  Mirror of `gradedMap` with the curve matrix. -/
noncomputable def gradedMapCurve (k n m : ℕ) (ωs : Fin n ↪ F) {L : ℕ}
    (f : Fin L → Fin n → F) (D DZ DW : ℕ) :
    (weigthBoundIndices k D × Fin (DZ + 1) → F) →ₗ[F]
      ((Fin n × constraintIndices m) × Fin (DW + 1) → F) where
  toFun x rc :=
    ((gsMatrixZCurve k n m ωs f D).mulVec (zVec k D DZ x) rc.1).coeff (rc.2 : ℕ)
  map_add' x y := by
    have hv : zVec k D DZ (x + y) = zVec k D DZ x + zVec k D DZ y := by
      funext p
      unfold zVec
      simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
    funext rc
    simp [hv, Matrix.mulVec_add]
  map_smul' a x := by
    have hv : zVec k D DZ (a • x) = a • zVec k D DZ x := by
      funext p
      unfold zVec
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, Polynomial.smul_monomial]
    funext rc
    simp [hv, Matrix.mulVec_smul, Polynomial.coeff_smul]

/-- Rank-nullity for the graded curve system: when the unknown count `|wBI|·(DZ+1)` exceeds
the equation count `n·|cI|·(DW+1)`, the graded map has a nonzero kernel vector. -/
theorem exists_nonzero_graded_kernel_curve {k n m L : ℕ} (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F) (D DZ DW : ℕ)
    (hcard : n * (constraintIndices m).card * (DW + 1) <
      (weigthBoundIndices k D).card * (DZ + 1)) :
    ∃ x : weigthBoundIndices k D × Fin (DZ + 1) → F,
      x ≠ 0 ∧ gradedMapCurve k n m ωs f D DZ DW x = 0 := by
  have h_kernel_nontrivial :
      Module.finrank F (weigthBoundIndices k D × Fin (DZ + 1) → F) >
        Module.finrank F ((Fin n × constraintIndices m) × Fin (DW + 1) → F) := by
    rw [Module.finrank_pi F, Module.finrank_pi F]
    simpa [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using hcard
  have h_inj : ¬ Function.Injective (gradedMapCurve k n m ωs f D DZ DW) := by
    intro h_inj
    exact h_kernel_nontrivial.not_ge
      (LinearMap.finrank_range_of_inj h_inj ▸ Submodule.finrank_le _)
  contrapose! h_inj
  exact LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr fun x hx ↦
    by_contra fun hx' ↦ h_inj x hx' <| by simpa using hx)

/-- Each `F[Z]`-valued Hasse constraint of the curve fold applied to a graded vector has
`Z`-degree at most `DZ + (L-1)·(D/(k-1))`: column entries have degree `≤ (L-1)·b` with
`b ≤ D/(k-1)`, and the vector has degree `≤ DZ`. -/
theorem mulVec_zVec_natDegree_le_curve {k n m L : ℕ} (hk : 1 < k) (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F) (D DZ : ℕ)
    (x : weigthBoundIndices k D × Fin (DZ + 1) → F) (ist : Fin n × constraintIndices m) :
    ((gsMatrixZCurve k n m ωs f D).mulVec (zVec k D DZ x) ist).natDegree ≤
      DZ + (L - 1) * (D / (k - 1)) := by
  simp only [Matrix.mulVec, dotProduct]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun p _ => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 := gsMatrixZCurve_natDegree_le_col ωs f D ist p
  have h2 := snd_le_div_of_mem_weigthBoundIndices hk p.2
  have h3 := zVec_natDegree_le k D DZ x p
  have h4 : (L - 1) * p.1.2 ≤ (L - 1) * (D / (k - 1)) := Nat.mul_le_mul_left _ h2
  omega

/-- **The `L`-ary graded Z-degree GS interpolant (#302): the curve-fold mirror.**

For the `L`-ary curve fold `∑ⱼ Zʲ·fⱼ` with `1 < k`, `n ≠ 0`, `1 ≤ m`, there is a *nonzero
integer* interpolant `Q₀ ∈ F[Z][X][Y]` whose image over `K = F(Z)` satisfies the
Guruswami–Sudan `Conditions` at the `gs_degree_bound`, and whose every `F[Z]`-coefficient
has `natDegree` at most `n·|constraintIndices m|·((L-1)·(gs_degree_bound k n m/(k-1)))`
— the pair
graded budget of `gs_existence_zDegree_graded` with exactly one extra factor `L-1` from the
curve point's `Z`-degree. -/
theorem gs_existence_zDegree_curve {n L : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (curveFold f)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      ∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤
        n * (constraintIndices m).card * ((L - 1) * (gs_degree_bound k n m / (k - 1))) := by
  classical
  set D := gs_degree_bound k n m with hD
  set DY := (L - 1) * (D / (k - 1)) with hDY
  set DZ := n * (constraintIndices m).card * DY with hDZ
  set DW := DZ + DY with hDW
  -- 1. the graded dimension count (parametric `graded_count`, at `DY := (L-1)·(D/(k-1))`)
  have hcount : numConstraints n m < numVars k D :=
    gs_numVars_gt_numConstraints_of_gt_one hn hk hm
  have hcard : n * (constraintIndices m).card * (DW + 1) <
      (weigthBoundIndices k D).card * (DZ + 1) := by
    rw [hDW, hDZ]
    exact graded_count (by simpa [numVars, numConstraints] using hcount)
  -- 2. a nonzero kernel vector of the graded F-linear system
  obtain ⟨x, hx0, hxker⟩ := exists_nonzero_graded_kernel_curve ωs f D DZ DW hcard
  set c' : weigthBoundIndices k D → F[X] := zVec k D DZ x with hc'
  -- 3. it assembles to a nonzero polynomial kernel vector of the F[Z]-matrix
  have hc'0 : c' ≠ 0 := by
    intro habs
    apply hx0
    funext pc
    have h1 : (c' pc.1).coeff (pc.2 : ℕ) = x (pc.1, pc.2) := by
      rw [hc']; exact zVec_coeff_fin x pc.1 pc.2
    rw [habs] at h1
    simpa using h1.symm
  have hdegW : ∀ ist : Fin n × constraintIndices m,
      ((gsMatrixZCurve k n m ωs f D).mulVec c' ist).natDegree ≤ DW := by
    intro ist
    rw [hc', hDW, hDY]
    exact mulVec_zVec_natDegree_le_curve hk ωs f D DZ x ist
  have hc'ker : (gsMatrixZCurve k n m ωs f D).mulVec c' = 0 := by
    funext ist
    rw [Pi.zero_apply]
    refine Polynomial.ext fun j => ?_
    rw [Polynomial.coeff_zero]
    by_cases hj : j < DW + 1
    · have h0 := congr_fun hxker (ist, (⟨j, hj⟩ : Fin (DW + 1)))
      simp only [gradedMapCurve, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
      rw [hc']
      exact h0
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hdegW ist) (by omega))
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
  have hck'' : constraintMap k n m (liftedDomain ωs) (curveFold f) D c'' = 0 := by
    funext i st
    have hrep := constraintMapCurve_eq_mulVec (k := k) (m := m) ωs f D c'' (i, st)
    rw [show constraintMap k n m (liftedDomain ωs) (curveFold f) D c'' i st =
        constraintMap k n m (liftedDomain ωs) (curveFold f) D c''
          ((i, st) : Fin n × constraintIndices m).1 ((i, st) : Fin n × constraintIndices m).2
      from rfl, hrep]
    show (((gsMatrixZCurve k n m ωs f D).map (algebraMap F[X] K)).mulVec c'') (i, st) = 0
    have : ((gsMatrixZCurve k n m ωs f D).map (algebraMap F[X] K)).mulVec c'' (i, st) =
        algebraMap F[X] K ((gsMatrixZCurve k n m ωs f D).mulVec c' (i, st)) := by
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
  · -- the graded Z-degree budget
    intro b a
    rw [hcoeff a b]
    by_cases h : (a, b) ∈ weigthBoundIndices k D
    · rw [dif_pos h, hc']
      exact zVec_natDegree_le k D DZ x ⟨(a, b), h⟩
    · rw [dif_neg h]
      simp

/-- **The `L`-ary `hbadz` producer (#302).** The curve-fold graded integer GS interpolant has
a degenerate set of cardinality at most
`n·|constraintIndices m|·((L-1)·(gs_degree_bound k n m/(k-1)))` — exactly the Z-degree-budget
input consumed by `exists_curve_cell_production_total` in `Hab25CurveCellProduction.lean`,
via `card_specialization_collapse_le`. -/
theorem gs_existence_zDegree_curve_card [Fintype F] {n L : ℕ} (k m : ℕ)
    (ωs : Fin n ↪ F) (f : Fin L → Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (curveFold f)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      (Finset.univ.filter (fun z : F =>
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0)).card ≤
        n * (constraintIndices m).card * ((L - 1) * (gs_degree_bound k n m / (k - 1))) := by
  obtain ⟨Q₀, h0, hcond, hdeg⟩ := gs_existence_zDegree_curve k m ωs f hk hn hm
  exact ⟨Q₀, h0, hcond, card_specialization_collapse_le h0 hdeg⟩

end GuruswamiSudan.OverRatFunc.ZDegree.Curve

-- Axiom audit anchors: every result is axiom-clean `[propext, Classical.choice, Quot.sound]`.
open GuruswamiSudan.OverRatFunc.ZDegree.Curve in
#print axioms intPointYCurve_natDegree_le
open GuruswamiSudan.OverRatFunc.ZDegree.Curve in
#print axioms gsMatrixZCurve_natDegree_le_col
open GuruswamiSudan.OverRatFunc.ZDegree.Curve in
#print axioms constraintMapCurve_eq_mulVec
open GuruswamiSudan.OverRatFunc.ZDegree.Curve in
#print axioms exists_nonzero_graded_kernel_curve
open GuruswamiSudan.OverRatFunc.ZDegree.Curve in
#print axioms mulVec_zVec_natDegree_le_curve
open GuruswamiSudan.OverRatFunc.ZDegree.Curve in
#print axioms gs_existence_zDegree_curve
open GuruswamiSudan.OverRatFunc.ZDegree.Curve in
#print axioms gs_existence_zDegree_curve_card
