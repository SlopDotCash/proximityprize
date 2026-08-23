/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon
/-!
# Issue #141 scratch: RS List-Decoding Beyond Johnson Radius

This file isolates the mathematical kernels surrounding the RS list-decoding capacity conjecture.
It formally establishes the "Johnson wall" gap (that capacity is strictly beyond the Johnson radius)
and extracts the necessary list-size bounds required to close the `epsMCAgsPrizeUniformConjecture`.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap
namespace Issue141

open NNReal

/-- The classical Johnson radius `1 - sqrt(ρ)`. -/
noncomputable def RSJohnsonRadius (ρ : ℝ≥0) : ℝ :=
  1 - Real.sqrt (ρ : ℝ)

/-- The capacity radius `1 - ρ - η`. -/
noncomputable def RSCapacityRadius (ρ η : ℝ≥0) : ℝ :=
  1 - (ρ : ℝ) - (η : ℝ)

/-- **The Johnson Wall Gap.**
This kernel formally proves that for `η < sqrt(ρ) - ρ`, the capacity radius is strictly
greater than the Johnson radius. This isolates exactly WHY the ABF26 uniform prize bound
requires mathematics beyond the classical Johnson bound (which tops out at `1 - sqrt(ρ)`).
-/
theorem capacity_strictly_beyond_johnson {ρ η : ℝ≥0} (h_rho : (ρ:ℝ) < 1) (h_rho_pos : 0 < (ρ:ℝ))
    (h_eta : (η : ℝ) < Real.sqrt (ρ : ℝ) - (ρ : ℝ)) :
    RSJohnsonRadius ρ < RSCapacityRadius ρ η := by
  unfold RSJohnsonRadius RSCapacityRadius
  linarith

/-- **The explicit polynomial list-size bound conjecture.**
The open core of Issue 141 is not just that a finite bound exists (which is true by finiteness),
but that a *uniform polynomial* bound exists independent of the field size for a given rate.
This defines the explicit polynomial kernel required for the grand challenge. -/
def UniformPolyListSizeConjecture (ρ η : ℝ≥0) : Prop :=
  ∃ (C d : ℝ), ∀ {ι F : Type} [Field F] [Fintype F] [Fintype ι]
    (domain : ι ↪ F) (w : ι → F),
    ((ListDecodable.closeCodewordsRel
        ((ReedSolomon.code (domain := domain) ⌊ρ * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
        w (RSCapacityRadius ρ η)).ncard : ℝ) ≤ C * ((Fintype.card ι : ℝ) ^ d)



end Issue141
end ProximityGap
