/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.HigherOrderMDSReedSolomon
import ArkLib.Data.CodingTheory.HigherOrderMDSOrderTwo

/-!
# The order-`k` extension of the single-interpolation-normal method (#389 / #407 R3)

`HigherOrderMDSOrderTwo.lean` shows order 2 is automatic and `HigherOrderMDSOrderThreeChar.lean`
closes order 3 for **pairs** via the single identity
`det(interpolation normals) = (sum,product) collinearity det`.  The pair picture there is special
to dimension `k = 3`: a pair `{a,b}` is a *codimension-1* set exactly when `card = k − 1`, i.e.
`2 = 3 − 1`.  This file isolates the honest, fully-general content of that method:

* `interpNormal D J` — the coefficient vector of `∏_{x∈J}(X − D x)` in `Fin k → K`, the
  interpolation normal of any **codimension-1** index set `J` (i.e. `J.card = k − 1`).  For
  `k = 3`, `card = 2`, this is exactly `pairNormal`; for `k`, `card = k − 1`, the row is the signed
  elementary-symmetric vector `(±e_{k-1}, …, −e_1, 1)` of the `k − 1` roots.

* `interpNormal_dot_col` / `frameSpan_dot_eq_zero` — the normal annihilates every RS column at a
  point of `J`, hence annihilates the whole `(k−1)`-dim pair-span.

* `isGenericInter_of_normalDet` — **the order-`k` certificate**: for `k` pairwise-disjoint
  codim-1 sets `J₀,…,J_{k-1}` of the RS frame in dimension `k`, if the `k × k` matrix of
  interpolation normals is nonsingular, the `k` hyperplanes meet only at `0` — order-`k` generic
  position.  This is the verbatim generalization of `isGenericInter_three_of_normalDet`.

So the *single-normal* method **does** extend to every order `k`, in its native codim-1 regime
(`card = k − 1`).  What it does **not** reach — and the precise obstruction the prompt asks for —
is the GM-MDS / list-decoding worst case, where the index sets keep a **fixed small card** (e.g.
pairs) while `k` grows: there each set is codim `k − card ≥ 2`, so its span is cut out by
`k − card` independent normals, not one, and order-`ℓ` generic position is governed by the
nonsingularity of a *non-square* stacked normal matrix / a generalized-Vandermonde **higher minor**
(the `LovettUnionDegreesInjective` / repeated-degree object), not a single scalar determinant.  The
header docstring records this boundary; `codim_frameSpan_eq_one_iff` pins the codim bookkeeping that
makes the single-determinant criterion square precisely at `card = k − 1`.

Axiom-clean.
-/

open Finset Module Matrix Polynomial ArkLib.HigherOrderMDS

namespace ArkLib.HigherOrderMDS

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vanishing polynomial of an index set `J`: `∏_{x∈J} (X − D x)`. -/
noncomputable def vanishPoly (D : ι → K) (J : Finset ι) : K[X] :=
  ∏ x ∈ J, (Polynomial.X - Polynomial.C (D x))

omit [Fintype ι] [DecidableEq ι] in
/-- `vanishPoly` is monic of degree `J.card`. -/
theorem vanishPoly_natDegree (D : ι → K) (J : Finset ι) :
    (vanishPoly D J).natDegree = J.card := by
  classical
  rw [vanishPoly]
  rw [Polynomial.natDegree_prod _ _ (fun x _ => Polynomial.X_sub_C_ne_zero (D x))]
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem vanishPoly_monic (D : ι → K) (J : Finset ι) : (vanishPoly D J).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C (D x))

omit [Fintype ι] [DecidableEq ι] in
/-- `vanishPoly D J` vanishes at `D x` for every `x ∈ J`. -/
theorem vanishPoly_eval_eq_zero (D : ι → K) (J : Finset ι) {x : ι} (hx : x ∈ J) :
    (vanishPoly D J).eval (D x) = 0 := by
  classical
  rw [vanishPoly, Polynomial.eval_prod]
  apply Finset.prod_eq_zero hx
  simp

/-- The **interpolation normal** of a codim-1 index set `J` (`J.card = k − 1`): the coefficient
vector of `∏_{x∈J}(X − D x)` read into `Fin k → K`.  For `k = 3, card = 2` this is `pairNormal`. -/
noncomputable def interpNormal (D : ι → K) (k : ℕ) (J : Finset ι) : Fin k → K :=
  fun j => (vanishPoly D J).coeff (j : ℕ)

omit [Fintype ι] [DecidableEq ι] in
/-- The top coefficient of the normal (`coeff (k−1)`) is `1` when `J.card = k − 1` (monic). -/
theorem interpNormal_top (D : ι → K) {k : ℕ} {J : Finset ι} (hcard : J.card = k - 1)
    (hk : 1 ≤ k) :
    interpNormal D k J ⟨k - 1, by omega⟩ = 1 := by
  have hdeg : (vanishPoly D J).natDegree = k - 1 := by rw [vanishPoly_natDegree, hcard]
  simp only [interpNormal]
  rw [← hdeg, (vanishPoly_monic D J).coeff_natDegree]

omit [Fintype ι] [DecidableEq ι] in
/-- **The normal annihilates the RS column at a point of `J`.**  `∑_j coeff_j · (D x)^j =
(vanishPoly).eval (D x) = 0` for `x ∈ J`, provided `deg = card ≤ k − 1` so the sum captures the
whole polynomial. -/
theorem interpNormal_dot_col (D : ι → K) {k : ℕ} {J : Finset ι} (hcard : J.card = k - 1)
    (hk : 1 ≤ k) {x : ι} (hx : x ∈ J) :
    interpNormal D k J ⬝ᵥ reedSolomonFrame D k x = 0 := by
  classical
  have hdeg : (vanishPoly D J).natDegree = k - 1 := by rw [vanishPoly_natDegree, hcard]
  -- the dot product is the evaluation of vanishPoly at D x via the coefficient/eval expansion
  have hsum : interpNormal D k J ⬝ᵥ reedSolomonFrame D k x
      = ∑ j : Fin k, (vanishPoly D J).coeff (j : ℕ) * (D x) ^ (j : ℕ) := by
    simp only [dotProduct, interpNormal, reedSolomonFrame]
  rw [hsum]
  -- eval of a polynomial of natDegree ≤ k-1 < k expands over Fin k
  have heval : (vanishPoly D J).eval (D x)
      = ∑ j ∈ Finset.range k, (vanishPoly D J).coeff j * (D x) ^ j := by
    rw [Polynomial.eval_eq_sum_range' (n := k) (by rw [hdeg]; omega)]
  rw [Finset.sum_range (fun j => (vanishPoly D J).coeff j * (D x) ^ j)] at heval
  rw [← heval, vanishPoly_eval_eq_zero D J hx]

omit [Fintype ι] [DecidableEq ι] in
/-- Every vector in the `J`-span (with `J.card = k − 1`) is annihilated by the interpolation
normal. -/
theorem frameSpan_dot_eq_zero (D : ι → K) {k : ℕ} {J : Finset ι} (hcard : J.card = k - 1)
    (hk : 1 ≤ k) {w : Fin k → K} (hw : w ∈ frameSpan K (reedSolomonFrame D k) J) :
    interpNormal D k J ⬝ᵥ w = 0 := by
  classical
  rw [frameSpan] at hw
  refine Submodule.span_induction
    (p := fun w _ => interpNormal D k J ⬝ᵥ w = 0) ?_ ?_ ?_ ?_ hw
  · rintro x ⟨ζ, hζ, rfl⟩
    rw [Finset.mem_coe] at hζ
    exact interpNormal_dot_col D hcard hk hζ
  · simp
  · intro x z _ _ hx hz; rw [dotProduct_add, hx, hz, add_zero]
  · intro c x _ hx; rw [dotProduct_smul, hx, smul_zero]

/-- The square `k × k` matrix of the `k` interpolation normals of `k` codim-1 index sets. -/
noncomputable def interpNormalMatrix (D : ι → K) (k : ℕ) (J : Fin k → Finset ι) :
    Matrix (Fin k) (Fin k) K :=
  Matrix.of (fun i j => interpNormal D k (J i) j)

/-- **The order-`k` generic-position certificate (the honest extension of the order-2,3 method).**
For `k` pairwise-disjoint codim-1 index sets `J₀,…,J_{k-1}` (`J i .card = k − 1`) of the RS frame in
dimension `k`, if the matrix of interpolation normals is nonsingular then the `k` hyperplanes meet
only at `0` — order-`k` generic intersection position.  Verbatim generalization of
`isGenericInter_three_of_normalDet` (which is the `k = 3`, `card = 2` instance). -/
theorem isGenericInter_of_normalDet (D : ι → K) (hD : Function.Injective D) {k : ℕ} (hk : 2 ≤ k)
    (J : Fin k → Finset ι) (hcard : ∀ i, (J i).card = k - 1)
    (hN : (interpNormalMatrix D k J).det ≠ 0) :
    IsGenericInter (fun i => frameSpan K (reedSolomonFrame D k) (J i)) := by
  classical
  set v := reedSolomonFrame D k with hv
  have hmds : IsMDSFrame K v := reedSolomonFrame_isMDS hD hk
  set N := interpNormalMatrix D k J with hNdef
  have hk1 : 1 ≤ k := by omega
  have hV : finrank K (Fin k → K) = k := by simp
  have hccard : ∀ i, (J i).card ≤ finrank K (Fin k → K) := by
    intro i; rw [hV, hcard i]; omega
  -- intersection is ⊥: any common vector is killed by the k independent normals
  have hbot : (⨅ i, frameSpan K v (J i)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_iInf] at hw
    have hker : N.mulVec w = 0 := by
      funext i
      have hwi : w ∈ frameSpan K v (J i) := hw i
      have := frameSpan_dot_eq_zero D (hcard i) hk1 hwi
      simpa [hNdef, interpNormalMatrix, Matrix.mulVec, dotProduct, interpNormal] using this
    have hunit : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr (isUnit_iff_ne_zero.mpr hN)
    have hinj := (Matrix.mulVec_injective_iff_isUnit (A := N)).2 hunit
    have : N.mulVec w = N.mulVec 0 := by rw [hker, Matrix.mulVec_zero]
    exact hinj this
  -- assemble generic position: each codim is 1, sum is k = dim, intersection ⊥
  have hcodim1 : ∀ i, codim (frameSpan K v (J i)) = 1 := by
    intro i
    rw [codim_frameSpan hmds (hccard i), hV, hcard i]; omega
  rw [IsGenericInter, hbot]
  -- LHS: codim ⊥ = finrank V - finrank ⊥ = k - 0 = k
  have hlhs : codim (⊥ : Submodule K (Fin k → K)) = k := by
    rw [codim, finrank_bot, hV]; omega
  -- RHS: ∑ codim = ∑ 1 = k
  have hrhs : (∑ i, codim (frameSpan K v (J i))) = k := by
    simp_rw [hcodim1]; simp
  rw [hlhs, hrhs, hV]; omega

/-- **Codim bookkeeping: why the single-determinant criterion is square exactly at `card = k − 1`.**
A `J`-span has dimension `J.card`, so it is cut out by `k − J.card` independent normals; the
single-normal / single-`k×k`-determinant method is available iff each set contributes exactly one
normal, i.e. `k − J.card = 1`.  This records that the order-`k` certificate above lives precisely in
the codim-1 regime, and pins the obstruction to extending it to the **fixed-small-card** GM-MDS
worst case (pairs with `k → ∞`, codim `k − 2 ≥ 2`), where the obstruction is a generalized-
Vandermonde *higher minor*, not a single scalar determinant. -/
theorem codim_frameSpan_eq_one_iff (D : ι → K) (hD : Function.Injective D) {k : ℕ} (hk : 2 ≤ k)
    {J : Finset ι} (hJ : J.card ≤ k) :
    codim (frameSpan K (reedSolomonFrame D k) J) = 1 ↔ J.card = k - 1 := by
  have hmds : IsMDSFrame K (reedSolomonFrame D k) := reedSolomonFrame_isMDS hD hk
  have hV : finrank K (Fin k → K) = k := by simp
  have hc : J.card ≤ finrank K (Fin k → K) := by rw [hV]; exact hJ
  rw [codim_frameSpan hmds hc, hV]
  omega

end ArkLib.HigherOrderMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.HigherOrderMDS.vanishPoly_natDegree
#print axioms ArkLib.HigherOrderMDS.interpNormal_dot_col
#print axioms ArkLib.HigherOrderMDS.frameSpan_dot_eq_zero
#print axioms ArkLib.HigherOrderMDS.isGenericInter_of_normalDet
#print axioms ArkLib.HigherOrderMDS.codim_frameSpan_eq_one_iff
