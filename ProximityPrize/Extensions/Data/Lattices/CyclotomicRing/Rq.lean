/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Lattices.CyclotomicRing.Rq

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Core.Basic
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# `Rq Φ` — the Cyclotomic Ring as a Computable `CommRing`

`ArkLib/Data/Lattices/CyclotomicRing/Basic.lean` gives a *semantic* cyclotomic ring
(`Φ.CyclotomicRing`, noncomputable) and a computable reduction `Φ.reduce`/`Φ.mul` on
raw `CPolynomial R`. Raw `CPolynomial` is not the right element type for a commitment
scheme: two raw polynomials can be unequal yet congruent mod `φ`, which would make the
binding reduction unsound (`s₁ - s₂` could be a nonzero multiple of `φ`).

This file fixes that by defining `Φ.Rq`, the subtype of **canonical reduced
representatives** `{ p : CPolynomial R // Φ.reduce p = p }`, and equipping it with a
genuine **computable `CommRing`** structure transported from the semantic quotient
along the injective ring map `a ↦ quotientHom a.val` (the CompPoly analogue of VCV-io's
`instCommRingPoly`).

## Main definitions

* `CyclotomicModulus.Rq Φ` — canonical reduced representatives of `R[X] / (φ)`.
* `CommRing (Φ.Rq)` — transported, computable; `+`/`*` are reduce-after-CPolynomial-op.
* `CyclotomicModulus.Rq.equivQuotient` — the ring iso `Φ.Rq ≃+* Φ.CyclotomicRing`.
-/

open Polynomial CompPoly CompPoly.CPolynomial

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-! ## `reduce` lemmas via the `toPoly` bridge -/

variable (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

namespace Rq

end Rq

end ArkLib.Lattices.CyclotomicModulus
