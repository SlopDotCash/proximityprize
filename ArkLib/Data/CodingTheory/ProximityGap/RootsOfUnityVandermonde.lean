/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Generalized Vandermonde determinants at roots of unity (#389)

The higher-order-MDS / GM-MDS conditions that certify Reed–Solomon list-decoding capacity are
*non-vanishings of generalized Vandermonde determinants* in the evaluation points. For a smooth
domain `μ_n` (the `n`-th roots of unity, the prize-relevant evaluation set) these determinants
factor through the cyclic symmetry, and this file proves the exact algebraic core of that
phenomenon:

> **`genVandermonde_rootsOfUnity_det`** — for a primitive `n`-th root of unity `ζ` and any
> exponent vector `e : Fin n → ℕ`, the determinant of `M i j = ζ ^ (e j * i)` is the Vandermonde
> product `∏_{i<j} (ζ^(e j) - ζ^(e i))`.
>
> **`genVandermonde_rootsOfUnity_det_ne_zero_iff`** — that determinant is nonzero **iff** the
> exponents are pairwise distinct modulo `n`.

The β-numbers `e_j = λ_j + (n-1-j)` of a partition `λ` are distinct mod `n` exactly when the
`n`-core of `λ` is empty (the combinatorial layer, in a companion development). Hence: the smooth
domain `μ_n` makes the HOMDS determinant vanish precisely on the partitions with nonempty
`n`-core — which are exactly the *interior-rectangle* shapes that govern list-decoding beyond the
Johnson bound. This is the exact, non-moment obstruction localized at the prize regime: the very
symmetry `x^n = 1` that makes the domain "smooth" annihilates the certificate.

Axiom-clean; pure linear algebra + primitive-root order arithmetic.
-/

open Matrix Finset

namespace ArkLib.ProximityGap.RootsOfUnityVandermonde

variable {F : Type*} [Field F] {n : ℕ}

/-- The generalized Vandermonde matrix `M i j = ζ ^ (e j * i)` at the roots of unity equals the
transpose of the standard Vandermonde matrix in the points `v j = ζ ^ (e j)`. -/
theorem genVandermonde_eq_transpose (ζ : F) (e : Fin n → ℕ) :
    (Matrix.of fun i j : Fin n => ζ ^ (e j * (i : ℕ)))
      = (Matrix.vandermonde (fun j => ζ ^ (e j)))ᵀ := by
  ext i j
  simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.vandermonde_apply, ← pow_mul]

/-- **Value form.** The generalized Vandermonde determinant at the roots of unity is the
Vandermonde product in `ζ^(e j)`. -/
theorem genVandermonde_rootsOfUnity_det (ζ : F) (e : Fin n → ℕ) :
    (Matrix.of fun i j : Fin n => ζ ^ (e j * (i : ℕ))).det
      = ∏ i : Fin n, ∏ j ∈ Ioi i, (ζ ^ (e j) - ζ ^ (e i)) := by
  rw [genVandermonde_eq_transpose, Matrix.det_transpose, Matrix.det_vandermonde]

/-- **Non-vanishing criterion.** For a primitive `n`-th root of unity `ζ`, the generalized
Vandermonde determinant `det (ζ ^ (e j * i))` is nonzero **iff** the exponents `e j` are pairwise
distinct modulo `n`. The cyclic symmetry is the whole content: `ζ^a = ζ^b ↔ a ≡ b [MOD n]`. -/
theorem genVandermonde_rootsOfUnity_det_ne_zero_iff [NeZero n] {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (e : Fin n → ℕ) :
    (Matrix.of fun i j : Fin n => ζ ^ (e j * (i : ℕ))).det ≠ 0
      ↔ Function.Injective (fun j => e j % n) := by
  rw [genVandermonde_eq_transpose, Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
  have key : ∀ a : ℕ, ζ ^ a = ζ ^ (a % n) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  constructor
  · intro hv i j hij
    apply hv
    show ζ ^ (e i) = ζ ^ (e j)
    rw [key (e i), key (e j)]
    exact congrArg (fun a => ζ ^ a) hij
  · intro hv i j hij
    apply hv
    show e i % n = e j % n
    have hmod : ζ ^ (e i % n) = ζ ^ (e j % n) := by rw [← key (e i), ← key (e j)]; exact hij
    exact hζ.pow_inj (Nat.mod_lt _ (NeZero.pos n)) (Nat.mod_lt _ (NeZero.pos n)) hmod

end ArkLib.ProximityGap.RootsOfUnityVandermonde
