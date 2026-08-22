/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R204 Gauss-period shift quarter sum)
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumDilationRecursion

/-!
# R204 (#466): Gauss-period quarter sums are invariant under nonzero frequency shifts

The dyadic dilation recursion has children

```text
left  b = ‖η_G(b)‖
right b = ‖η_G(ζ b)‖
```

for a nonzero dilation `ζ`.  On the full finite-field frequency set, multiplication
by `ζ` is a permutation, so the right child has exactly the same quarter-MGF sum
as the left child.  This is the concrete Gauss-period version of the abstract
R202/R203 shift-permutation input.
-/

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R204GaussPeriodShiftQuarterSum

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F]

/-- Full-frequency quarter-MGF sums of a Gauss-period spectrum are invariant
under a nonzero multiplicative shift of the frequency. -/
theorem quarter_sum_eta_shift_eq
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0) :
    (∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ G (ζ * b)‖))
      = ∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖) := by
  refine Finset.sum_nbij' (fun b : F => ζ * b) (fun c : F => ζ⁻¹ * c) ?_ ?_ ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro _ _
    exact Finset.mem_univ _
  · intro b _
    simp [hζ]
  · intro c _
    field_simp [hζ]
  · intro _ _
    rfl

/-- Inequality form consumed by shifted-quarter routes. -/
theorem quarter_sum_eta_shift_le
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0) :
    (∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ G (ζ * b)‖))
      ≤ ∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖) :=
  (quarter_sum_eta_shift_eq ψ G hζ).le

end ArkLib.ProximityGap.Frontier.R204GaussPeriodShiftQuarterSum

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R204GaussPeriodShiftQuarterSum.quarter_sum_eta_shift_eq
#print axioms ArkLib.ProximityGap.Frontier.R204GaussPeriodShiftQuarterSum.quarter_sum_eta_shift_le
