/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAZeroCodeUpperBound
import ArkLib.Data.CodingTheory.ProximityGap.MCAZeroCodeLowerBound

/-!
# The exact MCA error of the zero code (capstone)

Combining the tight upper bound (`MCAZeroCodeUpperBound`) and the matching construction
(`MCAZeroCodeLowerBound`), we obtain the **exact** value of the zero code's mutual-correlated-
agreement error, as a single named theorem:

  `ε_mca(⊥ over F, δ) = (⌊δ·n⌋ + 1)/|F|`,  for `δ ≤ 1` and `⌊δn⌋+1 ≤ min(|ι|, |F|)`,

with `n = |ι|`. This is the complete resolution of the MCA error for the zero code across the whole
admissible parameter range — and, in the Proximity-Prize sense, a fully machine-checked instance of
the Grand MCA Challenge format (a closed-form `ε_mca` from which the largest `δ*` with
`ε_mca ≤ ε*` is read off exactly).

## References
- Upper: `ProximityGap.MCAZeroCode.epsMCA_bot_le_floor_succ_div`.
- Lower: `ProximityGap.MCAZeroCode.epsMCA_bot_ge_floor_succ_div`.
- Issue #140 / #232.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAZeroCode

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Exact MCA error of the zero code.** `ε_mca(⊥, δ) = (⌊δn⌋+1)/|F|` for `δ ≤ 1` and
`⌊δn⌋+1 ≤ min(|ι|, |F|)`. -/
theorem epsMCA_bot_eq_floor_succ_div {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hkn : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ + 1 ≤ Fintype.card ι)
    (hkF : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ + 1 ≤ Fintype.card F) :
    epsMCA (F := F) (A := F) (Cbot : Set (ι → F)) δ
      = ((⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  le_antisymm (epsMCA_bot_le_floor_succ_div hδ1) (epsMCA_bot_ge_floor_succ_div hkn hkF)

#print axioms epsMCA_bot_eq_floor_succ_div

end ProximityGap.MCAZeroCode
