/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GK16Lemma12
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Guruswami-Wang affine-(s-1) solution-set pinning (GW BRICK-W, #93/#94)

The celebrated GW linear-algebraic core formalized: the GW functional-equation solution set is
affine with direction-space finrank <= s-1, via foldedWronskian_eq_zero_of_homogeneous composed
with the proven GK16 foldedWronskian_ne_zero_of_linearIndependent.
-/

/-!
# BRICK-W: the GW linear functional equation has an affine solution set of dim ≤ s-1

This file proves **BRICK-W** of the CZ25 / Guruswami–Wang `|L| > 1` capacity
list-decoding kernel (issue #93, `CZ25CoordFiberCap`).

## The GW linear functional equation

Fix a folding shift `σ(X) = γ · X` and coefficient polynomials `A₀, A₁, …, A_s ∈ F[X]`
with the nondegeneracy condition that the homogeneous coefficient family
`A : Fin s → F[X]`, `A j := A_{j+1}` is **not the zero family**.  The **substitution
operator** is

  `subst γ j p := p.comp (C (γ^j) · X) = p(γ^j · X)`,

an `F`-linear endomorphism of `F[X]`.  The **GW functional equation** for an unknown
`p` of degree `< k` is

  `A₀ + ∑_{j=0}^{s-1} A_{j+1} · p(γ^j · X) = 0`,

and its homogeneous part is `T_A p := ∑_{j} A j · subst γ j p = 0`.  The **solution set**

  `W := { p : degreeLT F k | A₀ + ∑_j A_{j+1} · p(γ^j X) = 0 }`

is the central object.

## Results

* `substLinear` — the substitution operator `p ↦ p(γ^j X)` as an `F`-linear map.
* `gwOperator` — the homogeneous functional-equation operator `T_A : F[X] →ₗ[F] F[X]`.
* `gwHomogSolution` — the homogeneous solution submodule `W₀ := ker T_A ⊓ degreeLT F k`.
* `gwSolutionSet` — the (inhomogeneous) solution set `W`, a set of polynomials.
* `foldedWronskian_eq_zero_of_homogeneous` — **the core link to the proven GK16
  substrate**: any family `p : Fin s → F[X]` of homogeneous solutions, with the
  coefficient family `A` nonzero, has *vanishing* folded Wronskian (the left-kernel
  vector `A` annihilates the dilation matrix, forcing `det = 0`).
* `gw_homogSolution_not_linearIndependent_of_card_s` — `s` homogeneous solutions are
  always `F`-linearly **dependent** (contradiction of the above with
  `foldedWronskian_ne_zero_of_linearIndependent`).
* `gw_solutionSet_finrank_le` — **the dimension bound**: `finrank W₀ ≤ s - 1`.
* `gw_solutionSet_affine` — **affineness**: `W` is an affine subspace, i.e. either empty
  or a coset `p₀ + W₀` of the homogeneous solution space `W₀`, whose direction space has
  `finrank ≤ s - 1`.

## References

- [GW13] Guruswami–Wang. *Linear-algebraic list decoding of folded Reed–Solomon codes.*
- [GK16] Guruswami–Kopparty. *Explicit Subspace Designs.* Lemma 12 (folded Wronskian).
-/

open Polynomial Matrix Module Submodule

namespace ArkLib.FRS.GK16.BrickW

variable {F : Type} [Field F]

/-! ## The substitution operator `p ↦ p(γ^j · X)` -/

/-- **The dilation/substitution operator `p ↦ p(γ^j · X)` as an `F`-linear endomorphism
of `F[X]`.**  This is the `j`-th component of the GW substitution operator
`p ↦ (p, p∘σ, …, p∘σ^{s-1})` for the folding shift `σ(X) = γ · X`. -/
noncomputable def substLinear (γ : F) (j : ℕ) : F[X] →ₗ[F] F[X] where
  toFun p := p.comp (Polynomial.C (γ ^ j) * Polynomial.X)
  map_add' p q := by simp [Polynomial.add_comp]
  map_smul' a p := by
    simp only [RingHom.id_apply, Polynomial.smul_comp]

@[simp] theorem substLinear_apply (γ : F) (j : ℕ) (p : F[X]) :
    substLinear γ j p = p.comp (Polynomial.C (γ ^ j) * Polynomial.X) := rfl

/-! ## The homogeneous GW functional-equation operator -/

/-- **The homogeneous GW functional-equation operator `T_A : F[X] →ₗ[F] F[X]`,**
`T_A p := ∑_{j} A j · p(γ^j · X)`.  The full (inhomogeneous) equation is
`A₀ + T_A p = 0`; the solution set is the affine fibre `T_A ⁻¹ {-A₀}`. -/
noncomputable def gwOperator {s : ℕ} (A : Fin s → F[X]) (γ : F) : F[X] →ₗ[F] F[X] :=
  ∑ j : Fin s, (LinearMap.mulLeft F (A j)) ∘ₗ substLinear γ (j : ℕ)

theorem gwOperator_apply {s : ℕ} (A : Fin s → F[X]) (γ : F) (p : F[X]) :
    gwOperator A γ p = ∑ j : Fin s, A j * p.comp (Polynomial.C (γ ^ (j : ℕ)) * Polynomial.X) := by
  simp only [gwOperator, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, substLinear_apply]

/-! ## The homogeneous solution submodule and the (affine) solution set -/

/-- **The homogeneous GW solution submodule** `W₀ := ker T_A ⊓ degreeLT F k`: degree-`< k`
polynomials `p` with `∑_j A j · p(γ^j X) = 0`.  This is the *direction space* of the
(affine) solution set `W`. -/
noncomputable def gwHomogSolution {s : ℕ} (A : Fin s → F[X]) (γ : F) (k : ℕ) :
    Submodule F F[X] :=
  LinearMap.ker (gwOperator A γ) ⊓ Polynomial.degreeLT F k

/-- **The (inhomogeneous) GW solution set** `W := { p ∈ degreeLT F k | A₀ + T_A p = 0 }`. -/
def gwSolutionSet {s : ℕ} (A₀ : F[X]) (A : Fin s → F[X]) (γ : F) (k : ℕ) : Set F[X] :=
  { p | p ∈ Polynomial.degreeLT F k ∧ A₀ + gwOperator A γ p = 0 }

theorem mem_gwSolutionSet {s : ℕ} (A₀ : F[X]) (A : Fin s → F[X]) (γ : F) (k : ℕ)
    {p : F[X]} :
    p ∈ gwSolutionSet A₀ A γ k ↔ p ∈ Polynomial.degreeLT F k ∧ A₀ + gwOperator A γ p = 0 :=
  Iff.rfl

/-! ## The core link to the proven GK16 substrate -/

/-- **The folded Wronskian of homogeneous solutions vanishes.**  If every column `p l`
of a family `p : Fin s → F[X]` satisfies the homogeneous functional equation
`∑_j A j · p l (γ^j X) = 0`, and the coefficient family `A` is **nonzero**, then the
folded Wronskian `foldedWronskian p γ` is zero.

*Proof.*  The folded Wronskian is `det M` for the dilation matrix
`M a l = (p l).comp (C (γ^a) · X) = p l (γ^a X)`.  The homogeneous equation for column
`l` says exactly that the `F[X]`-linear combination of the *rows* of `M` with coefficient
vector `A` vanishes in that column: `(A ᵥ* M) l = ∑_a A a · M a l = ∑_a A a · p l (γ^a X)
= 0`.  Hence `A ᵥ* M = 0` with `A ≠ 0`, so `det M = 0` by
`Matrix.exists_vecMul_eq_zero_iff`. -/
theorem foldedWronskian_eq_zero_of_homogeneous {s : ℕ}
    (A : Fin s → F[X]) (γ : F) (p : Fin s → F[X])
    (hA : A ≠ 0)
    (hsol : ∀ l, ∑ j : Fin s, A j * (p l).comp (Polynomial.C (γ ^ (j : ℕ)) * Polynomial.X) = 0) :
    foldedWronskian p γ = 0 := by
  classical
  unfold foldedWronskian
  set M : Matrix (Fin s) (Fin s) F[X] :=
    dilateMatrix p (fun a => Polynomial.C (γ ^ (a : ℕ)) * Polynomial.X) with hM
  -- The coefficient vector `A` is a nonzero left-kernel vector of `M`.
  have hvec : A ᵥ* M = 0 := by
    funext l
    simp only [Matrix.vecMul, dotProduct, hM, dilateMatrix, Pi.zero_apply]
    exact hsol l
  exact Matrix.exists_vecMul_eq_zero_iff.mp ⟨A, hA, hvec⟩

/-! ## `s` homogeneous solutions are linearly dependent -/

/-- **Any `s` homogeneous GW solutions are `F`-linearly dependent** (when the coefficient
family `A` is nonzero and `γ` is degree-separating).  A linearly *independent* family `p`
would have nonzero folded Wronskian by the proven hard direction of GK16 Lemma 12
(`foldedWronskian_ne_zero_of_linearIndependent`), contradicting
`foldedWronskian_eq_zero_of_homogeneous`. -/
theorem gw_homogSolution_not_linearIndependent_of_card_s {s : ℕ}
    (A : Fin s → F[X]) (γ : F) (p : Fin s → F[X])
    (hA : A ≠ 0)
    (hsol : ∀ l, ∑ j : Fin s, A j * (p l).comp (Polynomial.C (γ ^ (j : ℕ)) * Polynomial.X) = 0)
    (hγ_sep : ∀ Q : Fin s → F[X], (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => γ ^ (Q j).natDegree)) :
    ¬ LinearIndependent F p := by
  intro hindep
  have hWne : foldedWronskian p γ ≠ 0 :=
    foldedWronskian_ne_zero_of_linearIndependent p γ hindep hγ_sep
  exact hWne (foldedWronskian_eq_zero_of_homogeneous A γ p hA hsol)

/-! ## The dimension bound `finrank W₀ ≤ s - 1` -/

variable [DecidableEq F]

/-- Helper: membership in `gwHomogSolution` unfolds to the functional equation. -/
theorem mem_gwHomogSolution {s : ℕ} (A : Fin s → F[X]) (γ : F) (k : ℕ) {p : F[X]} :
    p ∈ gwHomogSolution A γ k ↔
      (∑ j : Fin s, A j * p.comp (Polynomial.C (γ ^ (j : ℕ)) * Polynomial.X) = 0)
        ∧ p ∈ Polynomial.degreeLT F k := by
  rw [gwHomogSolution, Submodule.mem_inf, LinearMap.mem_ker, gwOperator_apply]

/-- **BRICK-W, dimension bound: `finrank W₀ ≤ s - 1`.**

The homogeneous GW solution space `W₀ = ker T_A ⊓ degreeLT F k` has `F`-dimension at most
`s - 1`, where `s` is the number of folds (the length of the coefficient family `A`).

*Proof.*  Suppose not, so `finrank F W₀ ≥ s`.  A finite-dimensional space of `finrank ≥ s`
admits an `F`-linearly independent family `q : Fin s → W₀` of size `s` (the first `s`
vectors of a basis; here the truncation of a `finBasis`).  Pushing forward to `F[X]` gives
`s` linearly independent polynomials, each a homogeneous solution.  But
`gw_homogSolution_not_linearIndependent_of_card_s` forbids `s` independent homogeneous
solutions (under the nonzero-`A` and degree-separation hypotheses) — contradiction. -/
theorem gw_solutionSet_finrank_le {s : ℕ} (A : Fin s → F[X]) (γ : F) (k : ℕ)
    (hA : A ≠ 0)
    (hγ_sep : ∀ Q : Fin s → F[X], (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => γ ^ (Q j).natDegree)) :
    finrank F (gwHomogSolution A γ k) ≤ s - 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  -- `s ≤ finrank W₀`.
  have hs_le : s ≤ finrank F (gwHomogSolution A γ k) := by omega
  -- An `F`-linearly independent family of `s` vectors inside `W₀`.
  obtain ⟨q, hq_indep⟩ :
      ∃ q : Fin s → (gwHomogSolution A γ k),
        LinearIndependent F q := by
    -- Truncate a basis of `W₀` (of dimension ≥ s) to its first `s` members.
    haveI : FiniteDimensional F (Polynomial.degreeLT F k) := inferInstance
    haveI : FiniteDimensional F (gwHomogSolution A γ k) :=
      Submodule.finiteDimensional_inf_right _ _
    let n := finrank F (gwHomogSolution A γ k)
    let b : Basis (Fin n) F (gwHomogSolution A γ k) := finBasis F _
    have hle : s ≤ n := hs_le
    refine ⟨fun i => b (Fin.castLE hle i), ?_⟩
    exact b.linearIndependent.comp _ (Fin.castLE_injective hle)
  -- Push forward to `F[X]`.
  set p : Fin s → F[X] := fun l => ((q l : gwHomogSolution A γ k) : F[X]) with hp
  have hp_indep : LinearIndependent F p := by
    have := hq_indep.map' (gwHomogSolution A γ k).subtype
      (by rw [Submodule.ker_subtype])
    exact this
  -- Each `p l` is a homogeneous solution.
  have hsol : ∀ l, ∑ j : Fin s,
      A j * (p l).comp (Polynomial.C (γ ^ (j : ℕ)) * Polynomial.X) = 0 := by
    intro l
    have hmem : (q l : F[X]) ∈ gwHomogSolution A γ k := (q l).2
    rw [mem_gwHomogSolution] at hmem
    exact hmem.1
  exact gw_homogSolution_not_linearIndependent_of_card_s A γ p hA hsol hγ_sep hp_indep

/-! ## Affineness of the solution set -/

/-- **BRICK-W, affineness: `W` is an affine subspace.**  The GW solution set
`W = gwSolutionSet A₀ A γ k` is either empty, or — fixing any base solution `p₀ ∈ W` — the
coset `p₀ + W₀` of the homogeneous solution space `W₀ = gwHomogSolution A γ k`.  Concretely:
for any `p₀ ∈ W`, a polynomial `p` lies in `W` iff `p - p₀ ∈ W₀`.

This exhibits `W` as an affine `F`-subspace whose direction space is exactly `W₀`. -/
theorem gw_solutionSet_affine {s : ℕ} (A₀ : F[X]) (A : Fin s → F[X]) (γ : F) (k : ℕ)
    {p₀ : F[X]} (hp₀ : p₀ ∈ gwSolutionSet A₀ A γ k) :
    ∀ p, p ∈ gwSolutionSet A₀ A γ k ↔ (p - p₀) ∈ gwHomogSolution A γ k := by
  intro p
  rw [mem_gwSolutionSet] at hp₀ ⊢
  obtain ⟨hp₀deg, hp₀eq⟩ := hp₀
  rw [gwHomogSolution, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨hpdeg, hpeq⟩
    refine ⟨?_, (Polynomial.degreeLT F k).sub_mem hpdeg hp₀deg⟩
    rw [map_sub]
    -- `T_A p = -A₀ = T_A p₀`, so `T_A (p - p₀) = 0`.
    have h1 : gwOperator A γ p = -A₀ := by linear_combination hpeq
    have h0 : gwOperator A γ p₀ = -A₀ := by linear_combination hp₀eq
    rw [h1, h0, sub_self]
  · rintro ⟨hker, hdiff_deg⟩
    -- `p = (p - p₀) + p₀`; degree and equation both follow.
    have hp_deg : p ∈ Polynomial.degreeLT F k := by
      have : p = (p - p₀) + p₀ := by ring
      rw [this]
      exact (Polynomial.degreeLT F k).add_mem hdiff_deg hp₀deg
    refine ⟨hp_deg, ?_⟩
    have hTdiff : gwOperator A γ (p - p₀) = 0 := hker
    rw [map_sub] at hTdiff
    -- `T_A p = T_A p₀`, and `A₀ + T_A p₀ = 0`.
    have hTp : gwOperator A γ p = gwOperator A γ p₀ := by linear_combination hTdiff
    rw [hTp]; exact hp₀eq

/-- **BRICK-W, packaged: affine solution set of `finrank ≤ s - 1`.**  Combines
`gw_solutionSet_affine` (the solution set `W` is a coset of `W₀`) with
`gw_solutionSet_finrank_le` (`finrank W₀ ≤ s - 1`).  This is the complete BRICK-W deliverable:
the GW functional equation's solution set is affine with direction space of dimension `≤ s - 1`. -/
theorem gw_solutionSet_affine_finrank_le [DecidableEq F] {s : ℕ}
    (A₀ : F[X]) (A : Fin s → F[X]) (γ : F) (k : ℕ)
    (hA : A ≠ 0)
    (hγ_sep : ∀ Q : Fin s → F[X], (∀ j, Q j ≠ 0) →
        Function.Injective (fun j => (Q j).natDegree) →
        Function.Injective (fun j => γ ^ (Q j).natDegree)) :
    (∀ p₀ ∈ gwSolutionSet A₀ A γ k,
      ∀ p, p ∈ gwSolutionSet A₀ A γ k ↔ (p - p₀) ∈ gwHomogSolution A γ k)
    ∧ finrank F (gwHomogSolution A γ k) ≤ s - 1 :=
  ⟨fun _ hp₀ => gw_solutionSet_affine A₀ A γ k hp₀,
   gw_solutionSet_finrank_le A γ k hA hγ_sep⟩

end ArkLib.FRS.GK16.BrickW

-- Axiom audit (scratch only; remove before any migration).
