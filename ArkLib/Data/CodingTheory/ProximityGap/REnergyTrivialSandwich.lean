/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergyDiagonalFloor
import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTailReindexed

/-!
# The trivial sandwich for `rEnergy`

This file packages the two hypothesis-free ends of the additive-energy ladder in the same indexing:
for positive level `r+1`, the diagonal floor gives `|G|^(r+1) ≤ E_{r+1}`, while the char-p free-growth
ceiling gives `E_{r+1} ≤ |G|^(2r+1)`.  The gap between these two elementary bounds is exactly the
moment-method slack; the file makes no square-root-cancellation, CORE, or capacity claim.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false


open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy rEnergy_ge_card_pow)

namespace ArkLib.ProximityGap.REnergyTrivialSandwich

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Positive-level trivial sandwich for the `r`-fold additive energy.  The lower bound is the diagonal
`w = v`; the upper bound is the reindexed free-growth ceiling. -/
theorem rEnergy_succ_trivial_sandwich (G : Finset F) (r : ℕ) :
    G.card ^ (r + 1) ≤ rEnergy G (r + 1) ∧
      rEnergy G (r + 1) ≤ G.card ^ (2 * r + 1) := by
  exact ⟨rEnergy_ge_card_pow G (r + 1),
    ArkLib.ProximityGap.CharPDeepMomentTailReindexed.rEnergy_succ_le_pow_sharp G r⟩

/-- The same sandwich as an interval-membership statement, convenient for callers that want a single
`Set.Icc` fact. -/
theorem rEnergy_succ_mem_trivial_interval (G : Finset F) (r : ℕ) :
    rEnergy G (r + 1) ∈ Set.Icc (G.card ^ (r + 1)) (G.card ^ (2 * r + 1)) := by
  exact rEnergy_succ_trivial_sandwich G r

end ArkLib.ProximityGap.REnergyTrivialSandwich

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.REnergyTrivialSandwich.rEnergy_succ_trivial_sandwich
#print axioms ArkLib.ProximityGap.REnergyTrivialSandwich.rEnergy_succ_mem_trivial_interval
