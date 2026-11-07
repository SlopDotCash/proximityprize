/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefano Rocca
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Real.Sqrt

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ProximityPrize.Extensions.Data.CodingTheory.Basic.Distance
import ProximityPrize.Extensions.Data.CodingTheory.Basic.LinearCode
import ProximityPrize.Extensions.Data.CodingTheory.Basic.RelativeDistance
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import ProximityPrize.Extensions.Data.Polynomial.Bivariate
/-! # Guruswami-Sudan Basics -/


open Polynomial Polynomial.Bivariate Finsupp Finset

variable {F : Type} [Field F]
variable {k n m : ℕ}
variable {ωs : Fin n ↪ F}
variable {f : Fin n → F}

namespace GuruswamiSudan

section numVars

/-- Given a nonnegative integer `D`, it is the set of indices `(i,j)` such
    that `i + (k - 1) * j ≤ D`. -/
abbrev weigthBoundIndices (k D : ℕ) : Finset (ℕ × ℕ) :=
  weightBoundIndices k D

/-- The number of variables is the sum over j of the number of valid i's. -/
lemma card_weigthBoundIndices_eq_sum (D : ℕ) (hk : 1 < k) :
    (weigthBoundIndices k D).card = ∑ j ∈ range (D / (k - 1) + 1), (D - (k - 1) * j + 1) := by
  exact card_weightBoundIndices_eq_sum D hk

end numVars

section numConstraints

end numConstraints

section numVars_gt_numConstraints

end numVars_gt_numConstraints

section solution

end solution

section neZero

end neZero

section weightedDegree

end weightedDegree

section roots

end roots

section multiplicity

end multiplicity

section divisibility

open ReedSolomon

/-- The polynomial corresponding to a codeword has degree at most k-1. -/
lemma codewordToPoly_degree_le (hk : k + 1 ≤ n) (p : code ωs k) :
    (codewordToPoly p).natDegree ≤ k - 1 := by
  simpa only [codewordToPoly, toPolynomial_def, Function.Embedding.toFun_eq_coe] using
    (toPolynomial_degree_le (ωs := ωs) hk p)

end divisibility

section gs_rate

open ReedSolomon

end gs_rate

end GuruswamiSudan
