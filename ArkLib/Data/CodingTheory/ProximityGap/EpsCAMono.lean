/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Monotonicity of the correlated-agreement error in the fold-distance

The CA error `ε_ca(C, δ_fld, δ_int)` is monotone non-decreasing in the fold-distance `δ_fld`:
enlarging the fold-radius can only make the random line `u 0 + γ • u 1` *more* likely to be close
to `C`, while the `γ`-independent joint-proximity guard (controlled by `δ_int`) is untouched. This
is the CA analogue of the existing `epsMCA_mono`, and a basic API lemma for the §4 CA bounds.
-/

open scoped NNReal

set_option linter.unusedSectionVars false

namespace ProximityGap

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **`ε_ca` is monotone non-decreasing in the fold-distance `δ_fld`.** For `δ₁ ≤ δ₂` (and a fixed
interleaved-distance `δ_int`), `ε_ca(C, δ₁, δ_int) ≤ ε_ca(C, δ₂, δ_int)`. Per-stack: the
joint-proximity guard depends only on `δ_int`, so both terms take the same branch; on the
probability branch the event `Δᵣ(line, C) ≤ δ_fld` is monotone in `δ_fld`
(`Pr_le_Pr_of_implies`). -/
theorem epsCA_mono_fld (C : Set (ι → A)) (δ_int : ℝ≥0) {δ₁ δ₂ : ℝ≥0} (h : δ₁ ≤ δ₂) :
    epsCA (F := F) C δ₁ δ_int ≤ epsCA (F := F) C δ₂ δ_int := by
  unfold epsCA
  refine iSup_mono (fun u => ?_)
  split_ifs with hjp
  · exact le_refl 0
  · exact Pr_le_Pr_of_implies _ _ _ (fun γ hγ => le_trans hγ (by exact_mod_cast h))

end ProximityGap
