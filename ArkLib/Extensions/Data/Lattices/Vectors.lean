/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Lattices.Vectors

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Vectors And Matrices For The Lattice Layer

The lattice commitment layer uses **Mathlib function-vectors** `Fin k → P` and
`Matrix (Fin rows) (Fin cols) P` as containers, instantiated at the cyclotomic ring
`CyclotomicModulus.Rq Φ`. Using the canonical `Pi`/`Matrix` instance set avoids the
`Vector`-instance clash between Lean-core and `VCVio`, so the `0`/`-`/`+` used in the
Module-SIS relation are unambiguous.

To keep commitments **computable**, `dot`/`matVecMul`/`scalarVecMul` are defined over the
bare `Mul`/`Add`/`Zero` instances (via `List.sum ∘ List.ofFn`) rather than Mathlib's
`Matrix.mulVec` — the latter would route the ring product through the *noncomputable*
`Rq.commRing` instance. The linearity lemmas are proved over a `CommRing` carrier and
relate `dot` to `Finset.sum`.

## Main definitions

* `PolyVec` / `PolyMatrix` — `Fin`-indexed function-vector / matrix.
* `dot` / `matVecMul` / `scalarVecMul` — computable `⟨u,v⟩`, `M *ᵥ v`, `c • v`.
* `PolyVec.flattenBlocks` — flatten `blocks` equal-width blocks into one vector.
-/

open scoped BigOperators

universe u

namespace ArkLib.Lattices

namespace PolyVec

variable {P : Type u}

end PolyVec

/-! ## Computable vector / matrix arithmetic -/

section Defs

variable {P : Type u} [Mul P] [Add P] [Zero P]

end Defs

section Algebra

variable {P : Type u} [CommSemiring P]

end Algebra

section AlgebraRing

variable {P : Type u} [CommRing P]

end AlgebraRing

end ArkLib.Lattices
