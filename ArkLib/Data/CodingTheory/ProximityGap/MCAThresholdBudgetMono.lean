/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# Monotonicity of the MCA threshold `δ*` in the error budget `ε*` (#444 / #407)

`MCAThresholdLedger` brackets the MCA threshold `δ*(C, ε*) = sSup (mcaGoodRadii C ε*)` with proven
good/bad bounds along the RADIUS axis `δ` (`mca_good_set_downward_closed`,
`le_mcaDeltaStar_of_good`, `mcaDeltaStar_le_of_bad`).  It does NOT record the monotonicity along
the BUDGET axis `ε*`: that a more generous error budget can only raise the threshold.  This is
the load-bearing structural fact for any argument that transports a pin across budgets (e.g. a
tighter-budget pin implies the prize-budget pin), and is exactly the order-theoretic companion the
budget-vacuity delimiter (`CharSumBudgetVacuity`, O223) and the conditional pins
(`OpenCoreConditionalPin`, `PrizeConditionalPinCapstone`) consume implicitly.

## What is proved here (axiom-clean, no `sorry`)

* **`mcaGoodRadii_mono`** -- the good-radius SET is monotone in `ε*`: `ε*₀ ≤ ε*₁ ⟹
  mcaGoodRadii C ε*₀ ⊆ mcaGoodRadii C ε*₁` (a radius good under a tighter budget is good under a
  looser one).
* **`mcaDeltaStar_mono`** -- hence the threshold is monotone: `ε*₀ ≤ ε*₁ ⟹ δ*(C, ε*₀) ≤
  δ*(C, ε*₁)`.  A more generous budget never lowers `δ*`.
* **`mcaDeltaStar_le_of_budget_pin`** -- the transport consequence: a `δ*`-pin proven at a tighter
  budget `ε*₀ ≤ ε*₁` lower-bounds `δ*` at the looser budget too (so good radii survive budget
  relaxation); dually `mcaDeltaStar_le_of_bad` already gives the upper side.

## Honest scope (rule 3, rule 6)

Pure order theory on the ledger's own `sSup` object: a monotonicity infrastructure brick, NOT a CORE
touch and NOT thinness-specific (it holds for every code and every budget pair).  It does not bound
`ε_mca` or `δ*` at any concrete radius; it only records how `δ*` moves with the budget.  The genuine
open prize content (the realized worst-case incidence at the prize budget) is UNTOUCHED.  NON-MOMENT
infrastructure, EXTEND-proven on the proven in-tree ledger; NO moment/census/geometric-minor
re-derivation; NO capacity / beyond-Johnson / growth-law claim; cliff-at-n/2 untouched.
CORE `M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal
open ProximityGap

namespace ProximityGap.MCAThresholdLedger

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Good radii are monotone in the budget.**  If `ε*₀ ≤ ε*₁`, every radius that is good under the
tighter budget `ε*₀` (`ε_mca ≤ ε*₀`) is good under the looser budget `ε*₁` (`ε_mca ≤ ε*₁`). -/
theorem mcaGoodRadii_mono (C : Set (ι → A)) {εstar₀ εstar₁ : ℝ≥0∞} (hε : εstar₀ ≤ εstar₁) :
    mcaGoodRadii (F := F) (A := A) C εstar₀ ⊆ mcaGoodRadii (F := F) (A := A) C εstar₁ := by
  intro δ hδ
  exact ⟨hδ.1, le_trans hδ.2 hε⟩

/-- **The MCA threshold is monotone in the budget.**  A more generous error budget never lowers the
threshold: `ε*₀ ≤ ε*₁ ⟹ δ*(C, ε*₀) ≤ δ*(C, ε*₁)`.  Pure `sSup`-monotonicity over the budget-monotone
good-radius set, with the good set bounded above by `1`. -/
theorem mcaDeltaStar_mono (C : Set (ι → A)) {εstar₀ εstar₁ : ℝ≥0∞} (hε : εstar₀ ≤ εstar₁) :
    mcaDeltaStar (F := F) (A := A) C εstar₀ ≤ mcaDeltaStar (F := F) (A := A) C εstar₁ := by
  unfold mcaDeltaStar
  rcases (mcaGoodRadii (F := F) (A := A) C εstar₀).eq_empty_or_nonempty with hempty | hne
  · -- empty tighter set: `sSup ∅ = ⊥ = 0 ≤ _`.
    rw [hempty, csSup_empty]; exact bot_le
  · -- nonempty: standard `csSup` monotonicity over the budget-monotone subset.
    exact csSup_le_csSup (mcaGoodRadii_bddAbove (F := F) (A := A) C εstar₁) hne
      (mcaGoodRadii_mono (F := F) (A := A) C hε)

/-- **Budget transport of a `δ*` lower pin.**  A good radius `δ` proven under a tighter budget
`ε*₀ ≤ ε*₁` is also `≤ δ*` at the looser budget `ε*₁` -- the pin survives budget relaxation.
Routes `le_mcaDeltaStar_of_good` through `mcaDeltaStar_mono`. -/
theorem mcaDeltaStar_le_of_budget_pin (C : Set (ι → A)) {εstar₀ εstar₁ : ℝ≥0∞} {δ : ℝ≥0}
    (hε : εstar₀ ≤ εstar₁) (hδ : δ ≤ 1)
    (hgood : epsMCA (F := F) (A := A) C δ ≤ εstar₀) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C εstar₁ :=
  le_trans (le_mcaDeltaStar_of_good (F := F) (A := A) C εstar₀ hδ hgood)
    (mcaDeltaStar_mono (F := F) (A := A) C hε)

end ProximityGap.MCAThresholdLedger

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.MCAThresholdLedger.mcaGoodRadii_mono
#print axioms ProximityGap.MCAThresholdLedger.mcaDeltaStar_mono
#print axioms ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_budget_pin
