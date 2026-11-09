/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.MvPolynomial.Interpolation

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import ArkLib.Data.MvPolynomial.Degrees
import Mathlib.Data.FinEnum

/-!
  # Interpolation of multivariate polynomials

  Theory of interpolation for `MvPolynomial` with individual bounds on `degreeOf`. Follows from a
  combination of the univariate case (see `Lagrange.lean`) and the tensor structure of
  `MvPolynomial`.

  ## Main definitions

  ### Notation

  ## Tags
  multivariate polynomial, interpolation, multivariate Lagrange
-/

noncomputable section

namespace MvPolynomial

open Finset

section SchwartzZippel

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

end SchwartzZippel

section Vars

variable {σ : Type*}

-- Need more theorems about `MvPolynomial.vars`

-- Equivalence between `{p : R[X σ] | p.vars ⊆ s}` and `R[X {x : σ | x ∈ s}]`?
-- #check MvPolynomial.exists_fin_rename

end Vars

section MvPolynomialDetermination

variable {σ : Type*} [DecidableEq σ] [Fintype σ]
variable {R : Type*} [CommRing R] [IsDomain R]

section Finset

open Function Fintype

variable {n : ℕ}

open Polynomial
end Finset


end MvPolynomialDetermination

end MvPolynomial

end
