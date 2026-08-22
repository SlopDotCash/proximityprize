/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTail

/-!
# Reindexed consumer forms for the char-p deep moment tail

Small packaging brick for the unconditional moment lane.  The existing sharp tail theorem is stated with
an explicit positivity hypothesis `1 ≤ r`; downstream recursions usually index positive levels as
`r + 1`.  This file exposes that consumer form directly, avoiding repeated arithmetic rewrites while
preserving the same honest scope: the bound is the trivial moment tail, not a square-root-cancellation
or CORE claim.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)

namespace ArkLib.ProximityGap.CharPDeepMomentTailReindexed

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Reindexed sharp energy tail: `E_{r+1} ≤ |G|^(2r+1)`.  This is exactly
`CharPDeepMomentTail.rEnergy_le_pow_sharp` with the positive level written as `r+1`. -/
theorem rEnergy_succ_le_pow_sharp (G : Finset F) (r : ℕ) :
    rEnergy G (r + 1) ≤ G.card ^ (2 * r + 1) := by
  have h := ArkLib.ProximityGap.CharPDeepMomentTail.rEnergy_le_pow_sharp G (r + 1) (by omega)
  simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Reindexed sharp Gauss-moment tail: `‖η_b‖^(2(r+1)) ≤ q·|G|^(2r+1)`.  This is the
consumer form for positive moment levels indexed from zero. -/
theorem eta_pow_succ_le_sharp {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (b : F) :
    ‖eta ψ G b‖ ^ (2 * (r + 1)) ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r + 1) := by
  have h := ArkLib.ProximityGap.CharPDeepMomentTail.eta_pow2r_le_sharp hψ G (r + 1) (by omega) b
  simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end ArkLib.ProximityGap.CharPDeepMomentTailReindexed

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CharPDeepMomentTailReindexed.rEnergy_succ_le_pow_sharp
#print axioms ArkLib.ProximityGap.CharPDeepMomentTailReindexed.eta_pow_succ_le_sharp
