/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MaximalMinorIdealCertificate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceUnrestrictedKernelRefuted
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# From maximal minors to degree-restricted divided-difference rigidity

This file supplies the coefficient-space bridge missing between the symbolic maximal-minor
consumer and `DegreeAnchoredKernelRigid`.  After fixing two anchor components to zero, the source
columns are exactly the pairs `(non-anchor label, degree below K)`.  The canonical reconstruction
map turns such an array into a polynomial family, and the concrete gauged coefficient matrix is
the matrix of the support divided-difference operator after that reconstruction.

Consequently, injectivity of this concrete matrix implies degree-restricted anchored rigidity.
The final theorem composes that implication with a symbolic Vandermonde maximal-minor certificate.
It deliberately retains one explicit specialization equality: constructing a P1 symbolic matrix
and its Bezout certificate remains the open algebraic task.
-/

set_option autoImplicit false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.SupportDividedDifferenceMaximalMinorBridge

open MaximalMinorIdealCertificate
open SupportDividedDifferenceOperator
open SupportDividedDifferenceUnrestrictedKernelRefuted

variable {F X J : Type} [Field F] [DecidableEq J]

/-- Labels whose polynomial components remain after gauging the two anchors to zero. -/
abbrev GaugedLabel (a b : J) := {j : J // j ≠ a ∧ j ≠ b}

/-- Coefficient columns of the degree-`< K` two-anchor-gauged source. -/
abbrev GaugedColumn (a b : J) (K : Nat) := GaugedLabel a b × Fin K

/-- Package a label known not to be either anchor as a gauged label. -/
def gaugedLabelOfNotOr (a b j : J) (h : ¬(j = a ∨ j = b)) : GaugedLabel a b :=
  ⟨j, (not_or.mp h)⟩

/-- Read the non-anchor degree-`< K` coefficients of a polynomial family. -/
def gaugedCoefficientVector (a b : J) (K : Nat) (q : J -> F[X]) :
    GaugedColumn a b K -> F :=
  fun column => (q column.1.1).coeff column.2

/-- Reconstruct a degree-`< K` polynomial family from its non-anchor coefficient array, putting
the two anchor components equal to zero. -/
noncomputable def gaugedCoefficientFamily (a b : J) (K : Nat) :
    (GaugedColumn a b K -> F) →ₗ[F] (J -> F[X]) where
  toFun coefficients j := if h : j = a ∨ j = b then 0 else
    ((Polynomial.degreeLTEquiv F K).symm
      (fun d => coefficients (gaugedLabelOfNotOr a b j h, d))).1
  map_add' coefficients coefficients' := by
    funext j
    by_cases h : j = a ∨ j = b
    · simp only [h, ↓reduceDIte, Pi.add_apply, add_zero]
    · simp only [h, ↓reduceDIte, Pi.add_apply]
      let left : Fin K -> F := fun d =>
        coefficients (gaugedLabelOfNotOr a b j h, d)
      let right : Fin K -> F := fun d =>
        coefficients' (gaugedLabelOfNotOr a b j h, d)
      change ((Polynomial.degreeLTEquiv F K).symm (left + right)).1 =
        ((Polynomial.degreeLTEquiv F K).symm left).1 +
          ((Polynomial.degreeLTEquiv F K).symm right).1
      exact congrArg Subtype.val ((Polynomial.degreeLTEquiv F K).symm.map_add left right)
  map_smul' scalar coefficients := by
    funext j
    by_cases h : j = a ∨ j = b
    · simp only [h, ↓reduceDIte, Pi.smul_apply, smul_zero]
    · simp only [h, ↓reduceDIte, Pi.smul_apply]
      let vector : Fin K -> F := fun d =>
        coefficients (gaugedLabelOfNotOr a b j h, d)
      change ((Polynomial.degreeLTEquiv F K).symm (scalar • vector)).1 =
        scalar • ((Polynomial.degreeLTEquiv F K).symm vector).1
      exact congrArg Subtype.val ((Polynomial.degreeLTEquiv F K).symm.map_smul scalar vector)

@[simp]
theorem gaugedCoefficientFamily_anchor_left (a b : J) (K : Nat)
    (coefficients : GaugedColumn a b K -> F) :
    gaugedCoefficientFamily a b K coefficients a = 0 := by
  simp [gaugedCoefficientFamily]

@[simp]
theorem gaugedCoefficientFamily_anchor_right (a b : J) (K : Nat)
    (coefficients : GaugedColumn a b K -> F) :
    gaugedCoefficientFamily a b K coefficients b = 0 := by
  simp [gaugedCoefficientFamily]

/-- Every reconstructed component has degree below the column cutoff. -/
theorem gaugedCoefficientFamily_mem_degreeLT (a b : J) (K : Nat)
    (coefficients : GaugedColumn a b K -> F) (j : J) :
    gaugedCoefficientFamily a b K coefficients j ∈ Polynomial.degreeLT F K := by
  classical
  by_cases h : j = a ∨ j = b
  · rcases h with rfl | rfl <;> simp
  · change (if h' : j = a ∨ j = b then 0 else
      ((Polynomial.degreeLTEquiv F K).symm
        (fun d => coefficients (gaugedLabelOfNotOr a b j h', d))).1) ∈
        Polynomial.degreeLT F K
    rw [dif_neg h]
    exact ((Polynomial.degreeLTEquiv F K).symm
      (fun d => coefficients (gaugedLabelOfNotOr a b j h, d))).2

/-- Coefficient reconstruction is a left inverse on degree-`< K` families satisfying the anchor
gauge. -/
theorem gaugedCoefficientFamily_gaugedCoefficientVector
    [Fintype J] (a b : J) (K : Nat) (q : J -> F[X])
    (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F K)
    (hqa : q a = 0) (hqb : q b = 0) :
    gaugedCoefficientFamily a b K (gaugedCoefficientVector a b K q) = q := by
  funext j
  by_cases h : j = a ∨ j = b
  · rcases h with rfl | rfl
    · simpa using hqa.symm
    · simpa using hqb.symm
  · change (if h' : j = a ∨ j = b then 0 else
      ((Polynomial.degreeLTEquiv F K).symm
        (fun d => gaugedCoefficientVector a b K q
          (gaugedLabelOfNotOr a b j h', d))).1) = q j
    rw [dif_neg h]
    have heq :
        (Polynomial.degreeLTEquiv F K).symm
            (fun d => gaugedCoefficientVector a b K q
              (gaugedLabelOfNotOr a b j h, d)) =
          ⟨q j, hdegree j⟩ := by
      apply (Polynomial.degreeLTEquiv F K).injective
      funext d
      simp only [LinearEquiv.apply_symm_apply]
      change (q j).coeff d = (q j).coeff d
      rfl
    exact congrArg Subtype.val heq

/-- The divided-difference operator on reconstructed gauged coefficient arrays. -/
noncomputable def gaugedCoefficientOperator
    [Fintype J] (domain : X -> F) (support : X -> Finset J)
    (label : J -> F) (a b : J) (K : Nat) :
    (GaugedColumn a b K -> F) →ₗ[F] (SupportRow support -> F) :=
  (supportDividedDifference domain support label).comp
    (gaugedCoefficientFamily a b K)

/-- The exact concrete matrix whose maximal minors control degree-restricted anchored rigidity. -/
noncomputable def gaugedCoefficientMatrix
    [Fintype J] (domain : X -> F) (support : X -> Finset J)
    (label : J -> F) (a b : J) (K : Nat)
    [Fintype (GaugedColumn a b K)] [DecidableEq (GaugedColumn a b K)] :
    Matrix (SupportRow support) (GaugedColumn a b K) F :=
  LinearMap.toMatrix' (gaugedCoefficientOperator domain support label a b K)

/-- Matrix-vector multiplication by the concrete gauged coefficient matrix is definitionally the
support divided-difference operator applied to the reconstructed polynomial family. -/
theorem gaugedCoefficientMatrix_mulVec
    [Fintype J]
    (domain : X -> F) (support : X -> Finset J) (label : J -> F)
    (a b : J) (K : Nat) [Fintype (GaugedColumn a b K)]
    [DecidableEq (GaugedColumn a b K)]
    (coefficients : GaugedColumn a b K -> F) :
    (gaugedCoefficientMatrix domain support label a b K).mulVec coefficients =
      supportDividedDifference domain support label
        (gaugedCoefficientFamily a b K coefficients) := by
  simpa only [gaugedCoefficientMatrix, gaugedCoefficientOperator, LinearMap.comp_apply] using
    LinearMap.toMatrix'_mulVec
      (gaugedCoefficientOperator domain support label a b K) coefficients

/-- Exact evaluation equation for a gauged low-degree family: multiplying its coefficient vector
by the concrete matrix reproduces every support divided-difference row. -/
theorem gaugedCoefficientMatrix_mulVec_gaugedCoefficientVector
    [Fintype J]
    (domain : X -> F) (support : X -> Finset J) (label : J -> F)
    (a b : J) (K : Nat) [Fintype (GaugedColumn a b K)]
    [DecidableEq (GaugedColumn a b K)]
    (q : J -> F[X])
    (hdegree : ∀ j, q j ∈ Polynomial.degreeLT F K)
    (hqa : q a = 0) (hqb : q b = 0) :
    (gaugedCoefficientMatrix domain support label a b K).mulVec
        (gaugedCoefficientVector a b K q) =
      supportDividedDifference domain support label q := by
  rw [gaugedCoefficientMatrix_mulVec,
    gaugedCoefficientFamily_gaugedCoefficientVector a b K q hdegree hqa hqb]

/-- Injectivity of the exact concrete coefficient matrix discharges the corrected
degree-restricted anchored-kernel residual. -/
theorem degreeAnchoredKernelRigid_of_gaugedCoefficientMatrix_injective
    [Fintype J]
    (domain : X -> F) (support : X -> Finset J) (label : J -> F)
    (a b : J) (K : Nat) [Fintype (GaugedColumn a b K)]
    [DecidableEq (GaugedColumn a b K)]
    (hinjective : Function.Injective
      (gaugedCoefficientMatrix domain support label a b K).mulVec) :
    DegreeAnchoredKernelRigid domain support label K a b := by
  intro q hdegree hkernel hqa hqb
  have hmatrixZero :
      (gaugedCoefficientMatrix domain support label a b K).mulVec
          (gaugedCoefficientVector a b K q) = 0 := by
    rw [gaugedCoefficientMatrix_mulVec_gaugedCoefficientVector
      domain support label a b K q hdegree hqa hqb]
    exact LinearMap.mem_ker.mp hkernel
  have hcoeffZero : gaugedCoefficientVector a b K q = 0 := by
    apply hinjective
    simpa using hmatrixZero
  rw [← gaugedCoefficientFamily_gaugedCoefficientVector a b K q hdegree hqa hqb,
    hcoeffZero, map_zero]

/-! ## Explicit entries and canonical symbolic specialization -/

/-- The coefficient of one label component in a divided-difference row.  This definition works
over both the concrete field and the multivariate symbolic coefficient ring. -/
def rowLabelCoefficient {R : Type} [CommRing R] (label : J -> R)
    {support : X -> Finset J} (row : SupportRow support) (j : J) : R :=
  (if row.anchor₀ = j then label row.anchor₁ - label row.point else 0) +
    (if row.anchor₁ = j then label row.point - label row.anchor₀ else 0) +
    (if row.point = j then label row.anchor₀ - label row.anchor₁ else 0)

/-- A reconstructed coordinate vector has the expected monomial evaluation: the selected
non-anchor component evaluates to `x^d`, and every other component evaluates to zero. -/
theorem eval_gaugedCoefficientFamily_single
    (a b : J) (K : Nat) [Fintype (GaugedColumn a b K)]
    [DecidableEq (GaugedColumn a b K)]
    (column : GaugedColumn a b K) (j : J) (x : F) :
    (gaugedCoefficientFamily a b K
      (Pi.single (M := fun _ : GaugedColumn a b K => F) column 1) j).eval x =
      if j = column.1.1 then x ^ (column.2 : Nat) else 0 := by
  classical
  by_cases hanchor : j = a ∨ j = b
  · rcases hanchor with rfl | rfl
    · rw [gaugedCoefficientFamily_anchor_left, Polynomial.eval_zero,
        if_neg (Ne.symm column.1.2.1)]
    · rw [gaugedCoefficientFamily_anchor_right, Polynomial.eval_zero,
        if_neg (Ne.symm column.1.2.2)]
  · have hdegree := gaugedCoefficientFamily_mem_degreeLT (F := F)
      a b K (Pi.single (M := fun _ : GaugedColumn a b K => F) column 1) j
    rw [Polynomial.eval_eq_sum_degreeLTEquiv hdegree x]
    have hsubtype :
        (⟨gaugedCoefficientFamily a b K
            (Pi.single (M := fun _ : GaugedColumn a b K => F) column 1) j,
          hdegree⟩ : Polynomial.degreeLT F K) =
          (Polynomial.degreeLTEquiv F K).symm
            (fun d => Pi.single (M := fun _ : GaugedColumn a b K => F) column 1
              (gaugedLabelOfNotOr a b j hanchor, d)) := by
      apply Subtype.ext
      change (if h' : j = a ∨ j = b then 0 else
        ((Polynomial.degreeLTEquiv F K).symm
          (fun d => Pi.single (M := fun _ : GaugedColumn a b K => F) column 1
            (gaugedLabelOfNotOr a b j h', d))).1) = _
      rw [dif_neg hanchor]
    rw [hsubtype, LinearEquiv.apply_symm_apply]
    change (∑ d : Fin K,
      Pi.single (M := fun _ : GaugedColumn a b K => F) column 1
          (gaugedLabelOfNotOr a b j hanchor, d) *
        x ^ (d : Nat)) = _
    by_cases hj : j = column.1.1
    · subst j
      rw [if_pos rfl, Fintype.sum_eq_single column.2]
      · have hpair :
            (gaugedLabelOfNotOr a b column.1.1 hanchor, column.2) = column := by
          apply Prod.ext
          · apply Subtype.ext
            rfl
          · rfl
        simp [Pi.single_apply, hpair]
      · intro d hd
        have hpair : (gaugedLabelOfNotOr a b column.1.1 hanchor, d) ≠ column := by
          intro heq
          exact hd (congrArg Prod.snd heq)
        simp [Pi.single_apply, hpair]
    · rw [if_neg hj]
      apply Finset.sum_eq_zero
      intro d _hd
      have hpair : (gaugedLabelOfNotOr a b j hanchor, d) ≠ column := by
        intro heq
        exact hj (congrArg (fun c => c.1.1) heq)
      simp [Pi.single_apply, hpair]

/-- Every entry of the exact concrete matrix is a local label coefficient times the appropriate
Vandermonde monomial. -/
theorem gaugedCoefficientMatrix_apply
    [Fintype J] (domain : X -> F) (support : X -> Finset J) (label : J -> F)
    (a b : J) (K : Nat) [Fintype (GaugedColumn a b K)]
    [DecidableEq (GaugedColumn a b K)]
    (row : SupportRow support) (column : GaugedColumn a b K) :
    gaugedCoefficientMatrix domain support label a b K row column =
      rowLabelCoefficient label row column.1.1 *
        domain row.coordinate ^ (column.2 : Nat) := by
  rw [gaugedCoefficientMatrix, LinearMap.toMatrix'_apply]
  change dividedDifferenceAt domain label
    (gaugedCoefficientFamily a b K
      (Pi.single (M := fun _ : GaugedColumn a b K => F) column 1)) row = _
  simp only [dividedDifferenceAt, eval_gaugedCoefficientFamily_single]
  simp [rowLabelCoefficient, mul_add, add_mul]

/-- The canonical symbolic matrix: label scalars are variables, while the fixed domain points are
coefficients in the base field. -/
noncomputable def symbolicGaugedCoefficientMatrix
    [Fintype J] (domain : X -> F) (support : X -> Finset J)
    (a b : J) (K : Nat) [Fintype (GaugedColumn a b K)]
    [DecidableEq (GaugedColumn a b K)] :
    Matrix (SupportRow support) (GaugedColumn a b K) (MvPolynomial J F) :=
  fun row column =>
    rowLabelCoefficient (fun j => MvPolynomial.X j) row column.1.1 *
      MvPolynomial.C (domain row.coordinate ^ (column.2 : Nat))

/-- Specializing a symbolic local row coefficient evaluates each label variable to its concrete
label scalar. -/
theorem eval₂Hom_rowLabelCoefficient
    (label : J -> F) {support : X -> Finset J}
    (row : SupportRow support) (j : J) :
    MvPolynomial.eval₂Hom (RingHom.id F) label
        (rowLabelCoefficient (fun i => MvPolynomial.X i) row j) =
      rowLabelCoefficient label row j := by
  unfold rowLabelCoefficient
  by_cases h₀ : row.anchor₀ = j <;>
    by_cases h₁ : row.anchor₁ = j <;>
      by_cases hp : row.point = j <;> simp [h₀, h₁, hp]

/-- Evaluating the canonical symbolic matrix at concrete labels gives exactly the concrete matrix
of the reconstructed gauged support divided-difference operator. -/
theorem map_symbolicGaugedCoefficientMatrix
    [Fintype J] (domain : X -> F) (support : X -> Finset J) (label : J -> F)
    (a b : J) (K : Nat) [Fintype (GaugedColumn a b K)]
    [DecidableEq (GaugedColumn a b K)] :
    (symbolicGaugedCoefficientMatrix domain support a b K).map
        (MvPolynomial.eval₂Hom (RingHom.id F) label) =
      gaugedCoefficientMatrix domain support label a b K := by
  ext row column
  rw [gaugedCoefficientMatrix_apply]
  change MvPolynomial.eval₂Hom (RingHom.id F) label
      (rowLabelCoefficient (fun j => MvPolynomial.X j) row column.1.1 *
        MvPolynomial.C (domain row.coordinate ^ (column.2 : Nat))) = _
  rw [map_mul, eval₂Hom_rowLabelCoefficient, MvPolynomial.eval₂Hom_C]
  rfl

/-- **Symbolic maximal-minor bridge.**  A symbolic Vandermonde Bezout certificate implies the P1
degree-restricted rigidity target once the symbolic matrix is proved to specialize to the exact
concrete gauged coefficient matrix above.

The specialization equality and the certificate are intentionally separate hypotheses: this
theorem proves the full coefficient/matrix consumer, but does not claim that the P1 certificate
has already been constructed. -/
theorem degreeAnchoredKernelRigid_of_symbolicVandermonde_certificate
    {S : Type} [Fintype X] [Fintype J] [LinearOrder J]
    [Fintype S]
    (domain : X -> F) (support : X -> Finset J) (label : J -> F)
    (hlabel : Function.Injective label) (a b : J) (K : Nat)
    [Fintype (SupportRow support)] [Fintype (GaugedColumn a b K)]
    [DecidableEq (GaugedColumn a b K)]
    (symbolicMatrix :
      Matrix (SupportRow support) (GaugedColumn a b K) (MvPolynomial J F))
    (select : S -> GaugedColumn a b K -> SupportRow support)
    (coefficient : S -> MvPolynomial J F) (exponent : Nat)
    (hcertificate :
      symbolicVandermonde (F := F) (J := J) ^ exponent =
        ∑ s, coefficient s * (symbolicMatrix.submatrix (select s) id).det)
    (hspecialize :
      symbolicMatrix.map (MvPolynomial.eval₂Hom (RingHom.id F) label) =
        gaugedCoefficientMatrix domain support label a b K) :
    DegreeAnchoredKernelRigid domain support label K a b := by
  apply degreeAnchoredKernelRigid_of_gaugedCoefficientMatrix_injective
    domain support label a b K
  rw [← hspecialize]
  exact mulVec_injective_of_symbolicVandermonde_certificate
    (RingHom.id F) label hlabel symbolicMatrix select coefficient exponent hcertificate

/-- **Canonical certificate consumer.**  For the explicit symbolic matrix above, a
power-of-Vandermonde maximal-minor identity is now the only algebraic hypothesis needed to obtain
degree-restricted anchored rigidity. -/
theorem degreeAnchoredKernelRigid_of_canonicalSymbolicVandermonde_certificate
    {S : Type} [Fintype X] [Fintype J] [LinearOrder J] [Fintype S]
    (domain : X -> F) (support : X -> Finset J) (label : J -> F)
    (hlabel : Function.Injective label) (a b : J) (K : Nat)
    [Fintype (SupportRow support)] [Fintype (GaugedColumn a b K)]
    [DecidableEq (GaugedColumn a b K)]
    (select : S -> GaugedColumn a b K -> SupportRow support)
    (coefficient : S -> MvPolynomial J F) (exponent : Nat)
    (hcertificate :
      symbolicVandermonde (F := F) (J := J) ^ exponent =
        ∑ s, coefficient s *
          ((symbolicGaugedCoefficientMatrix domain support a b K).submatrix
            (select s) id).det) :
    DegreeAnchoredKernelRigid domain support label K a b := by
  apply degreeAnchoredKernelRigid_of_symbolicVandermonde_certificate
    domain support label hlabel a b K
    (symbolicGaugedCoefficientMatrix domain support a b K)
    select coefficient exponent hcertificate
  exact map_symbolicGaugedCoefficientMatrix domain support label a b K

end ArkLib.ProximityGap.Frontier.SupportDividedDifferenceMaximalMinorBridge

open ArkLib.ProximityGap.Frontier.SupportDividedDifferenceMaximalMinorBridge

#print axioms gaugedCoefficientFamily_gaugedCoefficientVector
#print axioms gaugedCoefficientMatrix_mulVec_gaugedCoefficientVector
#print axioms degreeAnchoredKernelRigid_of_gaugedCoefficientMatrix_injective
#print axioms gaugedCoefficientMatrix_apply
#print axioms map_symbolicGaugedCoefficientMatrix
#print axioms degreeAnchoredKernelRigid_of_symbolicVandermonde_certificate
#print axioms degreeAnchoredKernelRigid_of_canonicalSymbolicVandermonde_certificate
