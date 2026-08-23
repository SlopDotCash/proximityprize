/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# Interleaving stability of the MCA threshold ledger

The exact MCA interleaving invariance (`epsMCA_interleaved_eq`, [Jo26] ePrint 2026/891,
affine-line case) transfers verbatim to the formal threshold: the `δ*` of an interleaved
code equals the `δ*` of its base code, at every target error.  Every bracket recorded in
the threshold ledger — lower brackets from proven good radii, upper brackets such as the
below-capacity KKH26 ceiling — is therefore interleaving-stable with **no width factor**.

## Main result

* `mcaDeltaStar_interleaved_eq` — `δ*(C^≡t, ε*) = δ*(C, ε*)` for every `t ≥ 1` and every
  target `ε*`: the good-radius sets coincide pointwise (by the exact invariance of
  `ε_mca`), hence so do their suprema.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open Code

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The good-radius sets of an interleaved code and its base code coincide, by the exact
invariance `epsMCA_interleaved_eq`. -/
theorem mcaGoodRadii_interleaved_eq (C : Submodule F (ι → A)) (t : ℕ) [NeZero t]
    (εstar : ℝ≥0∞) :
    MCAThresholdLedger.mcaGoodRadii (F := F) (A := Fin t → A)
        ((C : Set (ι → A))^⋈ (Fin t)) εstar
      = MCAThresholdLedger.mcaGoodRadii (F := F) (A := A) (C : Set (ι → A)) εstar := by
  ext δ
  simp only [MCAThresholdLedger.mcaGoodRadii, Set.mem_setOf_eq,
    epsMCA_interleaved_eq C t δ]

/-- **The MCA threshold is exactly interleaving-stable.**  `δ*(C^≡t, ε*) = δ*(C, ε*)`:
every bracket in the threshold ledger transfers verbatim to row-wise interleaved codes,
with no interleaving-width factor.  ([Jo26] applied to the formal `δ*` of the ledger.) -/
theorem mcaDeltaStar_interleaved_eq (C : Submodule F (ι → A)) (t : ℕ) [NeZero t]
    (εstar : ℝ≥0∞) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := Fin t → A)
        ((C : Set (ι → A))^⋈ (Fin t)) εstar
      = MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) (C : Set (ι → A)) εstar := by
  unfold MCAThresholdLedger.mcaDeltaStar
  rw [mcaGoodRadii_interleaved_eq C t εstar]

end ProximityGap

/-! ## Axiom audit -/
#print axioms ProximityGap.mcaGoodRadii_interleaved_eq
#print axioms ProximityGap.mcaDeltaStar_interleaved_eq
