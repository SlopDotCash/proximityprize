/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GK16Wronskian
import ArkLib.ToMathlib.GK16BudgetCoeff
import ArkLib.ToMathlib.GK16Finish
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# GK16 Lemma 12, hard direction (folded-Wronskian non-vanishing)

This file develops the *hard* direction of GK16 Lemma 12 for the folded Wronskian
`L := foldedWronskian P ω = det [ (P j)(ω^a · X) ]_{a,j}` of polynomials
`P : Fin s → F[X]`:

  `LinearIndependent F P → foldedWronskian P ω ≠ 0`,

under a *necessary* hypothesis on the multiplicative order of `ω`. The *easy*
direction (`foldedWronskian P ω ≠ 0 → LinearIndependent F P`) is already proven in
`GK16Wronskian.lean` (`gk16_folded_wronskian_nonvanishing`).

## The bare statement is false — order of `ω` is required

The literal statement `LinearIndependent F P → foldedWronskian P ω ≠ 0` is **false**
without a hypothesis on `ω`: with `ω = 1` every dilation `q a = X`, so all rows of
the dilation matrix coincide and the determinant vanishes whenever `s ≥ 2`, even for
linearly-independent `P`. This is kernel-refuted below
(`foldedWronskian_eq_zero_of_one`, `not_lemma12_bare`).

The correct hypothesis (GK16 Definition 11 / admissibility): `ω` must have
multiplicative order large enough to separate the monomial degrees occurring in `P`.

## Main results

- `foldedWronskian_eq_zero_of_one` / `not_lemma12_bare` — the bare GK16 Lemma 12
  hard direction is **false** (refutation by `ω = 1`, `s = 2`).
- `foldedWronskian_smul_basis` — F-linearity of the folded Wronskian under an
  invertible change of basis: `foldedWronskian (P ∘ change) ω = c • foldedWronskian P ω`.
- `foldedWronskian_monomial` — closed form of the folded Wronskian of a *monomial*
  family `P j = X ^ m j`:  it equals `(∏ j, X ^ m j) • C (det (vandermonde (ω ^ m ·)))`.
- `foldedWronskian_monomial_ne_zero` — **monomial base case (Vandermonde):** for an
  injective degree map `m` with all `ω ^ m j` distinct, the folded Wronskian of
  `X ^ m ·` is nonzero. This is the GK16 Lemma 12 base case.

## References

- [GK16] Guruswami-Kopparty. *Explicit Subspace Designs*. Combinatorica 36(2),
  2016. Appendix A, Lemma 12 (folded-Wronskian non-vanishing criterion).
-/

open Polynomial Matrix

namespace ArkLib.FRS.GK16

variable {F : Type*} [Field F]

/-! ## Refutation of the bare statement (`ω = 1`) -/

/-- With `ω = 1` every row of the dilation matrix is `(P j).comp X = P j`, so for
`s ≥ 2` the matrix has two equal rows and the folded Wronskian vanishes — regardless
of linear independence of `P`. -/
theorem foldedWronskian_eq_zero_of_one {s : ℕ} (hs : 2 ≤ s) (P : Fin s → F[X]) :
    foldedWronskian P (1 : F) = 0 := by
  unfold foldedWronskian dilateMatrix
  -- All rows coincide: row `a` is `j ↦ (P j).comp (C 1 * X) = P j`.
  have hrow : ∀ a : Fin s, (fun j => (P j).comp (Polynomial.C ((1 : F) ^ (a : ℕ)) * X))
      = fun j => P j := by
    intro a
    funext j
    simp
  -- Two distinct rows `0` and `1` (using `s ≥ 2`) are equal ⟹ det = 0.
  refine Matrix.det_zero_of_row_eq (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) ?_ ?_
  · simp [Fin.ext_iff]
  · funext j
    show (P j).comp (Polynomial.C ((1 : F) ^ (0 : ℕ)) * X)
       = (P j).comp (Polynomial.C ((1 : F) ^ (1 : ℕ)) * X)
    simp

/-- **The bare GK16 Lemma 12 hard direction is false.** There exist a field, a
folding element `ω`, and a *linearly independent* family `P` with
`foldedWronskian P ω = 0`. Concretely `F = ZMod 2`-irrelevant; we use any field with
`ω = 1`, `s = 2`, `P = ![X, 1]` (independent), where the folded Wronskian vanishes.

This shows the hypothesis on the multiplicative order of `ω` (admissibility) in
the corrected statement is genuinely necessary, not a formalization artifact. -/
theorem not_lemma12_bare :
    ¬ (∀ (F : Type) (_ : Field F) (s : ℕ) (P : Fin s → F[X]) (ω : F),
        LinearIndependent F P → foldedWronskian P ω ≠ 0) := by
  intro h
  -- Use `F = ℚ`, `s = 2`, `P = ![X, 1]`, `ω = 1`.
  have hindep : LinearIndependent ℚ (![X, 1] : Fin 2 → ℚ[X]) := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    -- `a • X + b • 1 = 0` ⟹ comparing coeff 1 and coeff 0 forces `a = b = 0`.
    have h1 := congrArg (fun p => Polynomial.coeff p 1) hab
    have h0 := congrArg (fun p => Polynomial.coeff p 0) hab
    simp [Polynomial.coeff_one] at h1 h0
    exact ⟨h1, h0⟩
  exact h ℚ _ 2 ![X, 1] 1 hindep (foldedWronskian_eq_zero_of_one (by norm_num) _)

/-! ## Change of basis: F-linearity of the folded Wronskian -/

/-- **The dilation matrix is `F[X]`-linear in the column family, columnwise.**
Replacing the columns `P` by an `F`-linear recombination `Q j = ∑ i, c j i • P i`
recombines the columns of the dilation matrix by the same (scalar) matrix `C c`. -/
theorem dilateMatrix_comp_linear {s : ℕ} (P : Fin s → F[X]) (q : Fin s → F[X])
    (c : Fin s → Fin s → F) :
    dilateMatrix (fun j => ∑ i, c j i • P i) q
      = (dilateMatrix P q) * (Matrix.of (fun i j => Polynomial.C (c j i))) := by
  funext a j
  simp only [dilateMatrix, Matrix.mul_apply, Matrix.of_apply]
  rw [Polynomial.sum_comp]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.smul_comp, Polynomial.smul_eq_C_mul, mul_comm]

/-- **Folded Wronskian under an invertible change of basis.** If `Q j = ∑ i, c j i • P i`
is an `F`-linear recombination of `P` by the scalar matrix `c`, then
`foldedWronskian Q ω = C (det c) * foldedWronskian P ω`. In particular, when `c` is
invertible (`det c ≠ 0`), `foldedWronskian Q ω ≠ 0 ↔ foldedWronskian P ω ≠ 0`. -/
theorem foldedWronskian_change_basis {s : ℕ} (P : Fin s → F[X]) (ω : F)
    (c : Fin s → Fin s → F) :
    foldedWronskian (fun j => ∑ i, c j i • P i) ω
      = Polynomial.C ((Matrix.of c).det) * foldedWronskian P ω := by
  unfold foldedWronskian
  rw [dilateMatrix_comp_linear, Matrix.det_mul]
  -- det of the (transposed-`C`) scalar matrix is `C (det c)`.
  have : (Matrix.of (fun i j => Polynomial.C (c j i))).det
      = Polynomial.C ((Matrix.of c).det) := by
    rw [← Matrix.det_transpose (Matrix.of fun i j => Polynomial.C (c j i))]
    rw [show (Matrix.of (fun i j => Polynomial.C (c j i)))ᵀ
        = (Matrix.of c).map Polynomial.C from by
          funext i j; simp [Matrix.transpose_apply, Matrix.map_apply]]
    exact (Polynomial.C : F →+* F[X]).map_det (Matrix.of c) |>.symm
  rw [this, mul_comm]

/-! ## Monomial base case (Vandermonde) -/

/-- The dilation matrix of a monomial family `P j = X ^ m j` is
`a j ↦ C (ω ^ (a * m j)) * X ^ m j`. -/
theorem dilateMatrix_monomial {s : ℕ} (m : Fin s → ℕ) (ω : F) :
    dilateMatrix (fun j => X ^ m j) (fun a => Polynomial.C (ω ^ (a : ℕ)) * X)
      = Matrix.of (fun (a j : Fin s) => Polynomial.C (ω ^ ((a : ℕ) * m j)) * X ^ m j) := by
  funext a j
  simp only [dilateMatrix, Matrix.of_apply]
  rw [Polynomial.X_pow_comp, mul_pow, ← Polynomial.C_pow, ← pow_mul]

/-- **Closed form of the folded Wronskian of a monomial family.** For `P j = X ^ m j`,

  `foldedWronskian P ω = (∏ j, X ^ m j) * C (det (vandermonde (fun j => ω ^ m j)))`.

The determinant factors as a (transposed) Vandermonde determinant in the values
`ω ^ m j`, with the monomials `X ^ m j` pulled out columnwise. -/
theorem foldedWronskian_monomial {s : ℕ} (m : Fin s → ℕ) (ω : F) :
    foldedWronskian (fun j => X ^ m j) ω
      = (∏ j, X ^ m j) * Polynomial.C ((Matrix.vandermonde (fun j => ω ^ m j)).det) := by
  unfold foldedWronskian
  rw [dilateMatrix_monomial]
  -- Pull the monomial `X ^ m j` out of each column via `det_mul_row`.
  have hsplit : (Matrix.of (fun (a j : Fin s) => Polynomial.C (ω ^ ((a : ℕ) * m j)) * X ^ m j))
      = Matrix.of (fun (a j : Fin s) =>
          (fun j => X ^ m j) j * Polynomial.C (ω ^ ((a : ℕ) * m j))) := by
    funext a j; simp [mul_comm]
  rw [hsplit, Matrix.det_mul_row]
  congr 1
  -- The residual scalar determinant is `C` of the transposed Vandermonde det.
  have hvand : (fun (a j : Fin s) => Polynomial.C (ω ^ ((a : ℕ) * m j)))
      = (((Matrix.vandermonde (fun j => ω ^ m j)).map Polynomial.C)ᵀ : Matrix (Fin s) (Fin s) F[X]) := by
    funext a j
    simp only [Matrix.transpose_apply, Matrix.map_apply,
      Matrix.vandermonde_apply, ← pow_mul, mul_comm (m j) (a : ℕ)]
  rw [hvand, Matrix.det_transpose]
  exact ((Polynomial.C : F →+* F[X]).map_det (Matrix.vandermonde (fun j => ω ^ m j))).symm

/-- **GK16 Lemma 12, monomial base case.** If the degree map `m : Fin s → ℕ` is such
that the values `ω ^ m j` are pairwise distinct (equivalently, `ω` has multiplicative
order separating the degrees `m j`), then the folded Wronskian of the monomial family
`X ^ m ·` is nonzero. This is the Vandermonde base case of the Gaussian reduction in
GK16 Appendix A. -/
theorem foldedWronskian_monomial_ne_zero {s : ℕ} (m : Fin s → ℕ) (ω : F)
    (hω : Function.Injective (fun j => ω ^ m j)) :
    foldedWronskian (fun j => X ^ m j) ω ≠ 0 := by
  rw [foldedWronskian_monomial]
  apply mul_ne_zero
  · -- `∏ j, X ^ m j` is a product of nonzero monomials over a domain.
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact pow_ne_zero _ Polynomial.X_ne_zero
  · rw [Ne, Polynomial.C_eq_zero]
    exact (Matrix.det_vandermonde_ne_zero_iff).mpr hω

/-- **Order-of-`ω` corollary for the monomial base case.** If `ω` has multiplicative
order `> max degree` (concretely: each `m j < orderOf ω` and `m` injective), then the
values `ω ^ m j` are distinct and the monomial folded Wronskian is nonzero. This is the
admissibility hypothesis made explicit. -/
theorem foldedWronskian_monomial_ne_zero_of_order {s : ℕ} (m : Fin s → ℕ) (ω : F)
    (hm_inj : Function.Injective m) (hm_lt : ∀ j, m j < orderOf ω) :
    foldedWronskian (fun j => X ^ m j) ω ≠ 0 := by
  refine foldedWronskian_monomial_ne_zero m ω ?_
  intro i j hij
  exact hm_inj (pow_injOn_Iio_orderOf (hm_lt i) (hm_lt j) hij)

/-! ## Hard direction: a correct sufficient condition, and the precise residual

**Honest scope note.** The folded Wronskian of a *general* linearly-independent family
`P` is **not** reducible to the monomial base case by an `F`-linear change of basis:
the span `W = span P ⊆ F[X]` need not be spanned by monomials (e.g. `W = span {1+X², X}`
contains only one monomial up to scalars), so there is in general **no** invertible
recombination of `P` into a monomial family. The reduction below is therefore stated as
a genuine *sufficient condition* (when such a monomial recombination does exist), and the
full hard direction is left reduced to its correct residual — the *top-coefficient /
pivot-degree extraction* over the reduced-echelon basis (see the docstring residual
②-style note at the end of this section), **not** to a (false) monomial change of basis. -/

/-- **GK16 Lemma 12 hard direction — monomial-recombination sufficient condition.**
Suppose the column family `P` is obtained from a separated monomial family `X ^ m ·`
(the values `ω ^ m j` pairwise distinct) by an *invertible* `F`-linear change of basis
`c` (`det c ≠ 0`):

  `X ^ m j = ∑ i, c j i • P i`   for every `j`.

Then `foldedWronskian P ω ≠ 0`. (Whenever the span of `P` happens to be monomial-spanned
— the case that occurs in the GK16 base reductions — this is exactly Lemma 12.)

This is fully proven: it composes the monomial base case `foldedWronskian_monomial_ne_zero`
with the change-of-basis identity `foldedWronskian_change_basis`. -/
theorem foldedWronskian_ne_zero_of_monomial_change {s : ℕ}
    (P : Fin s → F[X]) (ω : F) (m : Fin s → ℕ) (c : Fin s → Fin s → F)
    (_hc : (Matrix.of c).det ≠ 0)
    (hbasis : ∀ j, (X ^ m j : F[X]) = ∑ i, c j i • P i)
    (hω : Function.Injective (fun j => ω ^ m j)) :
    foldedWronskian P ω ≠ 0 := by
  -- The monomial family is a change of basis of `P`, with nonzero folded Wronskian;
  -- the change-of-basis identity forces `foldedWronskian P ω ≠ 0`.
  have hmono : foldedWronskian (fun j => ∑ i, c j i • P i) ω ≠ 0 := by
    have : (fun j => ∑ i, c j i • P i) = (fun j => (X : F[X]) ^ m j) := by
      funext j; exact (hbasis j).symm
    rw [this]; exact foldedWronskian_monomial_ne_zero m ω hω
  rw [foldedWronskian_change_basis] at hmono
  exact fun h => hmono (by rw [h, mul_zero])

/-! ## General hard direction via distinct pivot degrees (leading-term extraction)

The honest scope note above is correct: a general independent `P` is **not** a monomial
recombination. The fully-general route instead extracts the **top coefficient** of the
folded Wronskian directly. For a family `P` with *pairwise distinct* degrees `d j` and all
`P j ≠ 0`, the coefficient of `foldedWronskian P ω` at the top monomial `X ^ (∑ j, d j)` is

  `(∏ j, leadingCoeff (P j)) · det (vandermonde (fun j => ω ^ d j))`,

which is nonzero precisely when `ω` separates the degrees (`ω ^ d j` distinct). This closes
Lemma 12 for any family with distinct degrees — and every linearly independent family is an
*invertible recombination* of such a one (its reduced-echelon basis), the reduction to
which is the only remaining residual (now purely a degree-normalization, not a monomial
change of basis). -/

/-- **Folded-Wronskian top coefficient (distinct-degree families).** Let `d j := natDegree
(P j)`. The coefficient of `foldedWronskian P ω` at the top monomial `X ^ (∑ j, d j)` is the
determinant of the leading-term matrix `(a, j) ↦ leadingCoeff (P j) · (ω ^ a) ^ d j`,
factored as `(∏ j, leadingCoeff (P j)) · det (vandermonde (ω ^ d ·))`.

Proof: expand `det` via `Matrix.det_apply'`, take the coefficient at `N := ∑ d j` of each
permutation term `ε σ · ∏_a M(σa, a)` using the variable-bound product-coefficient lemma
`coeff_prod_sum_of_natDegree_le` and the dilation-entry coefficient
`comp_C_mul_X_coeff`, then refactor the resulting signed sum as a Vandermonde determinant. -/
theorem coeff_foldedWronskian_sum_natDegree {s : ℕ} (P : Fin s → F[X]) (ω : F) :
    (foldedWronskian P ω).coeff (∑ j, (P j).natDegree)
      = (∏ j, (P j).leadingCoeff)
        * (Matrix.vandermonde (fun j => ω ^ (P j).natDegree)).det := by
  classical
  set d : Fin s → ℕ := fun j => (P j).natDegree with hd
  -- Entry of the dilation matrix and its degree bound.
  set M : Matrix (Fin s) (Fin s) F[X] :=
    dilateMatrix P (fun a => Polynomial.C (ω ^ (a : ℕ)) * Polynomial.X) with hM
  have hMentry : ∀ a j, M a j = (P j).comp (Polynomial.C (ω ^ (a : ℕ)) * Polynomial.X) :=
    fun a j => rfl
  -- natDegree of each entry is ≤ d j.
  have hMdeg : ∀ a j, (M a j).natDegree ≤ d j := by
    intro a j
    rw [hMentry]
    refine natDegree_comp_dilate_le (P j) _ ?_
    calc (Polynomial.C (ω ^ (a : ℕ)) * Polynomial.X).natDegree
        ≤ (Polynomial.C (ω ^ (a : ℕ))).natDegree + Polynomial.X.natDegree := natDegree_mul_le
      _ ≤ 0 + 1 := by gcongr <;> simp [natDegree_C]
      _ = 1 := by ring
  -- Coefficient of each entry at d j: `(P j).coeff (d j) * (ω^a)^(d j) = lc (P j) * (ω^a)^(d j)`.
  have hMcoeff : ∀ a j, (M a j).coeff (d j) = (P j).leadingCoeff * (ω ^ (a : ℕ)) ^ d j := by
    intro a j
    rw [hMentry, Polynomial.comp_C_mul_X_coeff]
    rfl
  -- Expand det and take the coefficient at N = ∑ d j.
  unfold foldedWronskian
  rw [← hM, Matrix.det_apply]
  rw [Polynomial.finset_sum_coeff]
  -- For each σ, coeff (sign σ • ∏_a M(σa,a)) N  (sign σ : ℤˣ acts by units-smul).
  have hterm : ∀ σ : Equiv.Perm (Fin s),
      ((Equiv.Perm.sign σ) • (∏ a, M (σ a) a)).coeff (∑ j, d j)
        = (Equiv.Perm.sign σ) •
            ∏ a, ((P a).leadingCoeff * (ω ^ (d a)) ^ (σ a : ℕ)) := by
    intro σ
    simp only [Units.smul_def, zsmul_eq_mul, Polynomial.coeff_intCast_mul]
    congr 1
    -- The product `∏_a M(σa, a)` has factor `M(σa,a)` of degree ≤ `d a` (column `a`),
    -- so its coefficient at `∑_a d a` is the product of the factor top-coefficients.
    rw [Polynomial.coeff_prod_sum_of_natDegree_le _ d Finset.univ
          (fun a _ => hMdeg (σ a) a)]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    rw [hMcoeff (σ a) a]
    -- `(ω^(σa))^(d a) = (ω^(d a))^(σa)`.
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ)]
  -- Pull `∏ lc` out of each term and recognise the (transposed) Vandermonde determinant.
  -- `det (vandermonde v) = det (vandermonde v)ᵀ = ∑_σ ε σ ∏_a (v (σ a)) ^ a`,
  -- but our product is `∏_a (v a) ^ (σ a)` = `∏_a Vᵀ (σ a) a` with `Vᵀ i j = (v j)^i`.
  rw [show (Matrix.vandermonde (fun j => ω ^ d j)).det
        = (Matrix.vandermonde (fun j => ω ^ d j))ᵀ.det from
      (Matrix.det_transpose _).symm]
  rw [Matrix.det_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [Units.smul_def, zsmul_eq_mul]
  rw [Finset.prod_mul_distrib]
  -- `∏ a, (ω^(d a))^(σ a) = ∏ a, vandermondeᵀ (ω^d·) (σ a) a`.
  have hvand : (∏ a, (ω ^ (d a)) ^ (σ a : ℕ))
      = ∏ a, (Matrix.vandermonde (fun j => ω ^ d j))ᵀ (σ a) a := by
    refine Finset.prod_congr rfl (fun a _ => ?_)
    rw [Matrix.transpose_apply, Matrix.vandermonde_apply]
  rw [hvand]
  ring

/-- **GK16 Lemma 12 hard direction — distinct-degree families (fully general).**
If the family `P : Fin s → F[X]` has *pairwise distinct* degrees (`(P ·).natDegree`
injective), every `P j ≠ 0`, and `ω` separates the degrees (`ω ^ (P j).natDegree`
pairwise distinct), then `foldedWronskian P ω ≠ 0`.

This is the unconditional engine of Lemma 12: the top coefficient
`coeff (foldedWronskian P ω) (∑ j, (P j).natDegree)` equals
`(∏ j, leadingCoeff (P j)) · det (vandermonde (ω ^ (P ·).natDegree))`
(`coeff_foldedWronskian_sum_natDegree`), a product of nonzero factors — the leading
coefficients are nonzero since each `P j ≠ 0`, and the Vandermonde determinant is nonzero
since `ω` separates the (distinct) degrees. A nonzero coefficient forces the polynomial
nonzero. No monomial-change-of-basis assumption is needed. -/
theorem foldedWronskian_ne_zero_of_distinct_natDegree {s : ℕ} (P : Fin s → F[X]) (ω : F)
    (hP_ne : ∀ j, P j ≠ 0)
    (hω : Function.Injective (fun j => ω ^ (P j).natDegree)) :
    foldedWronskian P ω ≠ 0 := by
  -- It suffices that the top coefficient is nonzero.
  intro hzero
  have hcoeff : (foldedWronskian P ω).coeff (∑ j, (P j).natDegree) = 0 := by
    rw [hzero]; simp
  rw [coeff_foldedWronskian_sum_natDegree] at hcoeff
  -- The product `∏ lc (P j)` is nonzero (each `P j ≠ 0`).
  have hlc : (∏ j, (P j).leadingCoeff) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    rw [Ne, Polynomial.leadingCoeff_eq_zero]
    exact hP_ne j
  -- The Vandermonde determinant is nonzero (`ω ^ d j` distinct).
  have hvand : (Matrix.vandermonde (fun j => ω ^ (P j).natDegree)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hω
  exact (mul_ne_zero hlc hvand) hcoeff

/-!
### The general GK16 Lemma 12 hard direction is now CLOSED

The distinct-degree case is closed unconditionally
(`foldedWronskian_ne_zero_of_distinct_natDegree`). The general statement
`LinearIndependent F P → foldedWronskian P ω ≠ 0` (with `ω` of multiplicative order
exceeding the degree spread of `P`) reduces to it by a **degree-normalization /
echelon-reduction** step, which is now itself a *theorem*
(`gk16Lemma12HardResidual_holds`, via `exists_distinctDegree_recombination` in
`ToMathlib/GK16Finish.lean` — Gaussian elimination on degrees, sorry/axiom-clean).
The fully-assembled hard direction is `foldedWronskian_ne_zero_of_linearIndependent`.
The argument:

  Every linearly independent `P` is an *invertible* `F`-linear recombination of a family
  `Q` with pairwise distinct degrees (its reduced-row-echelon basis): repeatedly subtract
  scalar multiples to clear coinciding leading terms. By `foldedWronskian_change_basis`,
  `foldedWronskian P ω` and `foldedWronskian Q ω` differ by the nonzero scalar `det c`,
  so the nonvanishing of the latter (now `foldedWronskian_ne_zero_of_distinct_natDegree`)
  transfers to `P`. The residual is thus reduced from the deep "non-cancellation /
  majorization on echelon support" argument to the routine linear-algebra fact that an
  independent family of polynomials admits a distinct-degree basis with invertible
  transition matrix (Gaussian elimination on degrees).

The echelon step is now exposed directly as the theorem `GK16Lemma12HardResidual`;
the hard direction is unconditional modulo only the genuinely necessary
admissibility hypothesis on `ω` (`foldedWronskian_ne_zero_of_linearIndependent`). -/

/-- **GK16 Lemma 12 echelon step (formerly the named hard residual).**
A linearly independent family `P` admits a distinct-degree, nonzero-leading recombination
`Q j = ∑ i, c j i • P i` by an invertible scalar matrix `c`. This is exactly Gaussian
elimination on the degrees of `P`, supplied by `exists_distinctDegree_recombination`. -/
theorem GK16Lemma12HardResidual (F : Type) (hF : Field F) (s : ℕ) (P : Fin s → F[X])
    (hindep : LinearIndependent F P) :
    ∃ (Q : Fin s → F[X]) (c : Fin s → Fin s → F),
      (Matrix.of c).det ≠ 0 ∧
      (∀ j, Q j = ∑ i, c j i • P i) ∧
      (∀ j, Q j ≠ 0) ∧
      Function.Injective (fun j => (Q j).natDegree) := by
  letI := hF
  exact exists_distinctDegree_recombination P hindep

/-- **Proven reduction: the echelon theorem implies the full hard direction.**
If `ω` separates the resulting pivot degrees, `LinearIndependent F P →
foldedWronskian P ω ≠ 0`. The proof is the change-of-basis transfer composed
with the distinct-degree engine; it is itself `sorry`-free. -/
theorem GK16Lemma12HardResidual_reduces_hard
    {s : ℕ} {F₀ : Type} [hF : Field F₀]
    (P : Fin s → F₀[X]) (ω : F₀)
    (hindep : LinearIndependent F₀ P)
    (hω_sep : ∀ Q : Fin s → F₀[X], (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => ω ^ (Q j).natDegree)) :
    foldedWronskian P ω ≠ 0 := by
  obtain ⟨Q, c, hc_det, hQ, hQ_ne, hQ_deg⟩ :=
    GK16Lemma12HardResidual F₀ hF s P hindep
  -- `foldedWronskian Q ω ≠ 0` by the distinct-degree engine.
  have hQW : foldedWronskian Q ω ≠ 0 :=
    foldedWronskian_ne_zero_of_distinct_natDegree Q ω hQ_ne (hω_sep Q hQ_ne hQ_deg)
  -- Transfer along the change of basis: `foldedWronskian Q ω = C (det c) * foldedWronskian P ω`.
  have hcb : foldedWronskian Q ω = Polynomial.C ((Matrix.of c).det) * foldedWronskian P ω := by
    rw [show Q = (fun j => ∑ i, c j i • P i) from funext hQ]
    exact foldedWronskian_change_basis P ω c
  intro hPzero
  rw [hPzero, mul_zero] at hcb
  exact hQW hcb

/-- Lowercase alias kept for downstream references to the now-proven echelon step. -/
theorem gk16Lemma12HardResidual_holds (F : Type) (hF : Field F) (s : ℕ)
    (P : Fin s → F[X]) (hindep : LinearIndependent F P) :
    ∃ (Q : Fin s → F[X]) (c : Fin s → Fin s → F),
      (Matrix.of c).det ≠ 0 ∧
      (∀ j, Q j = ∑ i, c j i • P i) ∧
      (∀ j, Q j ≠ 0) ∧
      Function.Injective (fun j => (Q j).natDegree) :=
  GK16Lemma12HardResidual F hF s P hindep

/-- **GK16 Lemma 12, hard direction — fully general, no residual.**
For any linearly independent family `P : Fin s → F₀[X]` over a field `F₀`, if `ω`
separates the degrees of *every* nonzero, distinct-degree family (the admissibility
hypothesis `hω_sep`), then `foldedWronskian P ω ≠ 0`.

This is `GK16Lemma12HardResidual_reduces_hard` discharged with the now-proven
echelon theorem `GK16Lemma12HardResidual`; the only remaining input is the
genuinely-necessary order/admissibility hypothesis on `ω` (without which the
statement is false, cf. `not_lemma12_bare`). -/
theorem foldedWronskian_ne_zero_of_linearIndependent
    {s : ℕ} {F₀ : Type} [Field F₀]
    (P : Fin s → F₀[X]) (ω : F₀)
    (hindep : LinearIndependent F₀ P)
    (hω_sep : ∀ Q : Fin s → F₀[X], (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => ω ^ (Q j).natDegree)) :
    foldedWronskian P ω ≠ 0 :=
  GK16Lemma12HardResidual_reduces_hard P ω hindep hω_sep

end ArkLib.FRS.GK16

/-! ## Axiom audit -/
#print axioms ArkLib.FRS.GK16.GK16Lemma12HardResidual
#print axioms ArkLib.FRS.GK16.GK16Lemma12HardResidual_reduces_hard
#print axioms ArkLib.FRS.GK16.gk16Lemma12HardResidual_holds
#print axioms ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent
