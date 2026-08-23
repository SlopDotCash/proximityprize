/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettPolynomial
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Lovett's GM-MDS proof: the base case m = 1 (#389, layer 4)

Theorem 1.7 of Lovett (arXiv:1803.02523) over the polynomial ring `F[a]` (equivalent to
over `F(a)` by clearing denominators — p.3 remark — avoiding the fraction field).  The
**base case `m = 1`**: for a single multiplicity vector `v`, the shifted family
`{ pVanish v · xᵉ : e < N }` is linearly independent over `F[a]`.

Mechanism: `{xᵉ}` are independent (sub-family of `Polynomial.basisMonomials`) and
multiplication by the nonzero monic `pVanish v` is an injective `F[a]`-linear map.

Issue #389.
-/

open Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n : ℕ}

/-- The powers `{xᵉ : e < N}` are linearly independent over the coefficient ring. -/
theorem xpow_linearIndependent (R : Type*) [CommRing R] (N : ℕ) :
    LinearIndependent R (fun e : Fin N => (Polynomial.X : R[X]) ^ (e : ℕ)) := by
  have h := (Polynomial.basisMonomials R).linearIndependent.comp
    (fun e : Fin N => (e : ℕ)) Fin.val_injective
  have heq : (fun e : Fin N => (Polynomial.X : R[X]) ^ (e : ℕ))
      = (⇑(Polynomial.basisMonomials R)) ∘ (fun e : Fin N => (e : ℕ)) := by
    funext e
    simp only [Function.comp_apply, Polynomial.coe_basisMonomials]
    exact X_pow_eq_monomial _
  rw [heq]; exact h

/-- **Base case `m = 1` of Theorem 1.7.**  The single-vector shifted family
`{ pVanish v · xᵉ : e < N }` is linearly independent over `F[a]`.  Proof: factor out the
nonzero monic `pVanish v` and cancel in the domain, reducing to monomial independence. -/
theorem pFam_single_linearIndependent (v : Fin n → ℕ) (N : ℕ) :
    LinearIndependent (MvPolynomial (Fin n) F) (fun e : Fin N => pFam (F := F) v (e : ℕ)) := by
  classical
  have hmon := xpow_linearIndependent (MvPolynomial (Fin n) F) N
  rw [Fintype.linearIndependent_iff] at hmon ⊢
  intro g hg i
  refine hmon g ?_ i
  have key : pVanish (F := F) v
      * (∑ e, g e • (Polynomial.X : (MvPolynomial (Fin n) F)[X]) ^ (e : ℕ)) = 0 := by
    rw [Finset.mul_sum]
    have hsum : (∑ e, pVanish (F := F) v
          * (g e • (Polynomial.X : (MvPolynomial (Fin n) F)[X]) ^ (e : ℕ)))
        = ∑ e, g e • pFam (F := F) v (e : ℕ) :=
      Finset.sum_congr rfl (fun e _ => by
        rw [pFam]; exact Algebra.mul_smul_comm (g e) (pVanish (F := F) v) _)
    rw [hsum]; exact hg
  exact (mul_eq_zero.mp key).resolve_left (pVanish_monic (F := F) v).ne_zero

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.pFam_single_linearIndependent
