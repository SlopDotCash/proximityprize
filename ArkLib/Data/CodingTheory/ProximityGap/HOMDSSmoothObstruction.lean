/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RootsOfUnityVandermonde
import ArkLib.Data.CodingTheory.ProximityGap.AbacusNCore

/-!
# The smooth-domain HOMDS obstruction (#389): the exact `n`-core dichotomy

This file fuses the two companion developments into the headline statement of the exact-algebraic
prize obstruction. For a smooth domain `μ_n` (the `n`-th roots of unity) and a partition `λ` with
β-numbers `β_j = λ_j + (n-1-j)`, the higher-order-MDS / GM-MDS certificate is the generalized
Vandermonde determinant `det (ζ ^ (β_j · i))`. We prove:

> **`homds_det_ne_zero_iff_nCoreEmpty`** — that determinant is nonzero **iff** the abacus
> `n`-core of `λ` (presented by `β`) is empty.

Equivalently (`homds_det_eq_zero_iff_nCore_nonempty`): the certificate **vanishes iff the
`n`-core is nonempty**. Since the list-decoding-beyond-Johnson extremal shapes are interior
rectangles, whose `n`-cores are nonempty, the smooth domain `μ_n` makes the HOMDS certificate
vanish exactly in the capacity regime: the cyclic symmetry `x^n = 1` that makes the domain
"smooth" is precisely what annihilates the certificate. This is the non-moment wall, now
machine-checked end to end, complementing the √-lossy moment walls W1–W4.

Axiom-clean.
-/

open Matrix Finset
open ArkLib.ProximityGap.RootsOfUnityVandermonde
open ArkLib.ProximityGap.AbacusNCore

namespace ArkLib.ProximityGap.HOMDSSmoothObstruction

variable {F : Type*} [Field F] {n : ℕ}

/-- **The exact `n`-core dichotomy.** For a primitive `n`-th root of unity `ζ` and β-numbers
`β : Fin n → ℕ`, the higher-order-MDS determinant `det (ζ ^ (β_j · i))` is nonzero **iff** the
abacus `n`-core (presented by `β`) is empty. -/
theorem homds_det_ne_zero_iff_nCoreEmpty [NeZero n] {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (β : Fin n → ℕ) :
    (Matrix.of fun i j : Fin n => ζ ^ (β j * (i : ℕ))).det ≠ 0 ↔ nCoreEmpty β := by
  rw [genVandermonde_rootsOfUnity_det_ne_zero_iff hζ, nCoreEmpty_iff_injOn_mod]

/-- **Contrapositive form.** At a smooth domain `μ_n`, the HOMDS certificate **vanishes iff the
`n`-core is nonempty** — the exact non-moment obstruction. -/
theorem homds_det_eq_zero_iff_nCore_nonempty [NeZero n] {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (β : Fin n → ℕ) :
    (Matrix.of fun i j : Fin n => ζ ^ (β j * (i : ℕ))).det = 0 ↔ ¬ nCoreEmpty β := by
  rw [← homds_det_ne_zero_iff_nCoreEmpty hζ β, not_not]

end ArkLib.ProximityGap.HOMDSSmoothObstruction
