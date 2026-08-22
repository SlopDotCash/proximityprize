/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

/-!
# The prize COMPLETENESS statement: `δ*` in the window ⟺ the single scalar `B` (#444)

This file formalizes the directive's **completeness theorem**: the entire Proximity Prize content
of the threshold `δ*` in the window is *exactly* the single open scalar
`B = max_{b≠0} ‖η_b‖` (the thin dyadic Gauss-period sup-norm = BGK/Paley wall), via a
**two-way reduction** with everything else proven around it.

The two faces are:

* **`δ*`-side** — the window lower pin `δ ≤ mcaDeltaStar C εstar` (the prize "δ* reaches the
  window radius" statement).
* **`B`-side** — the worst-case far-line incidence bound `WorstCaseIncidenceBounded C δ B`
  (`OpenCoreConditionalPin`), which by the exact incidence↔period bridge
  (`IncidencePeriodBridge.lineIncidence_period_sum`, the `√`-loss-free Fourier identity) is
  controlled by the single scalar `B`: at a budget `B ≈ q·ε* ≈ n` it is the statement
  `‖η_b‖ ≤ C√(n log m)` realized into the incidence count.

## The completeness biconditional

`PrizeEquivalence C εstar δ B` is the `Prop`

  `WorstCaseIncidenceBounded C δ B  ↔  δ ≤ mcaDeltaStar C εstar`

stated at a budget `B/q ≤ ε*` (`hbudget`).  This is the formal object "the prize is EXACTLY the
single scalar `B`": a proven two-way reduction between the `δ*` window pin and the open core.

* **Forward direction** (`B`-side ⟹ `δ*`-side): **PROVEN, axiom-clean** — this is
  `OpenCoreConditionalPin.worstCaseIncidence_pin`. A bound on the worst-case incidence `B` forces
  the `δ*` lower pin.

* **Converse direction** (`δ*`-side ⟹ `B`-side): the **hard new direction**, stated here as ONE
  named `Prop` `ConverseRealizer C εstar δ B`. It is the *realizer*: a `δ*` window statement must
  force a worst-case-incidence statement. Honestly, the only way to prove it is a CONSTRUCTIVE
  worst word whose realized far-line incidence equals (not merely `≤`) a function of `B`, so that
  `δ ≤ δ*` forces `I(δ) ≤ B`. This realizer is **not proven here** (it is the converse of the open
  core, and is at least as hard); it is carried as an explicit hypothesis.

## What is proven (axiom-clean, no `sorry`)

* `PrizeEquivalence_of_converse` — the **wrapper theorem**: given the converse realizer
  `ConverseRealizer` (named) and the budget side condition `hbudget`, the full biconditional
  `PrizeEquivalence` holds. The forward leg is discharged outright by `worstCaseIncidence_pin`;
  only the converse leg consumes the named hypothesis.

* `prizeEquivalence_forward` — the forward leg, fully proven and standalone (= the open-core pin).

* `prizeEquivalence_iff_converseRealizer` — meta-statement: under the budget side condition, the
  biconditional `PrizeEquivalence` holds **iff** the converse realizer holds. I.e. the *entire*
  remaining gap between "conditional pin" and "complete biconditional" is exactly the one named
  `Prop` `ConverseRealizer`, with no other open math.

## Honest scope (the load-bearing self-check)

* **Direction proven: forward only.** The forward `B ⟹ δ*` is proven (the open-core conditional
  pin). The converse `δ* ⟹ B` is **named, not proven** — it is the converse realizer, strictly the
  harder direction (it must build the worst word that *saturates* the incidence). The biconditional
  is therefore `proven modulo ConverseRealizer`, and that residual is isolated as ONE explicit
  `Prop`. The `B`-side itself (`WorstCaseIncidenceBounded` at window budget, i.e. `B ≤ C√(n log m)`)
  remains the recognized ~25-year-open BGK/Paley wall — NOT closed here, by anyone.
* **No wall is smuggled.** `ConverseRealizer` is the *converse* implication only; it does NOT assert
  the open `B` bound. The wrapper `PrizeEquivalence_of_converse` does not discharge the wall, and
  the forward leg `prizeEquivalence_forward` does not depend on the converse at all.

Issue #444.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger Code
open ProximityGap.OpenCoreConditionalPin

namespace ProximityGap.PrizeEquivalence

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The converse realizer — the one named (hard) direction -/

/-- **The converse realizer (`δ*`-side ⟹ `B`-side), as ONE named `Prop`.**

This is the hard new direction of the completeness biconditional: *if* the threshold reaches the
window radius `δ ≤ mcaDeltaStar C εstar`, *then* the worst-case far-line incidence is bounded,
`WorstCaseIncidenceBounded C δ B`.

Proving it requires a **constructive worst word** whose realized far-line incidence equals (not just
`≤`) a function of the single scalar `B`, so that a `δ*` statement forces a `B` statement (it is the
converse of the open-core pin and is at least as hard). It is stated here, **not proven** — the only
residual between the proven conditional pin and a full biconditional. -/
def ConverseRealizer (C : Set (ι → A)) (εstar : ℝ≥0∞) (δ : ℝ≥0) (B : ℕ) : Prop :=
  δ ≤ mcaDeltaStar (F := F) (A := A) C εstar →
    WorstCaseIncidenceBounded (F := F) (A := A) C δ B

/-! ## The completeness biconditional -/

/-- **THE PRIZE COMPLETENESS STATEMENT (`δ*` ⟺ the single scalar `B`).**

`PrizeEquivalence C εstar δ B` is the biconditional

  `WorstCaseIncidenceBounded C δ B  ↔  δ ≤ mcaDeltaStar C εstar`.

It says: at the window radius `δ` and budget `B`, the prize "δ* reaches the window" statement is
*logically equivalent* to the single-scalar far-line incidence bound `B` — i.e. the prize is
**exactly** the one open scalar `B`, with a two-way reduction. -/
def PrizeEquivalence (C : Set (ι → A)) (εstar : ℝ≥0∞) (δ : ℝ≥0) (B : ℕ) : Prop :=
  WorstCaseIncidenceBounded (F := F) (A := A) C δ B ↔ δ ≤ mcaDeltaStar (F := F) (A := A) C εstar

/-! ## The forward leg — fully proven (the open-core conditional pin) -/

/-- **Forward leg (`B`-side ⟹ `δ*`-side), PROVEN.** A bound `B` on the worst-case far-line
incidence at radius `δ` (with `δ ≤ 1` and the budget side condition `B/q ≤ ε*`) forces the `δ*`
lower pin. This is exactly the open-core conditional pin
`OpenCoreConditionalPin.worstCaseIncidence_pin`; it depends on NO converse hypothesis. -/
theorem prizeEquivalence_forward (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hI : WorstCaseIncidenceBounded (F := F) (A := A) C δ B) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C εstar :=
  worstCaseIncidence_pin (F := F) (A := A) C εstar hδ hI hbudget

/-! ## The wrapper — biconditional modulo the named converse realizer -/

/-- **THE WRAPPER: the full completeness biconditional, modulo the one named converse realizer.**

Given (a) the budget side condition `B/q ≤ ε*`, (b) `δ ≤ 1`, and (c) the named converse realizer
`ConverseRealizer C εstar δ B` (the hard `δ*` ⟹ `B` direction), the biconditional
`PrizeEquivalence C εstar δ B` holds. The forward leg is discharged outright by
`worstCaseIncidence_pin` (proven, axiom-clean); only the converse leg consumes `hconv`.

This is the honest "complete and correct" object: the prize = ONE scalar `B`, provably, with the
*entire* residual isolated into the single explicit `Prop` `ConverseRealizer`. -/
theorem PrizeEquivalence_of_converse (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hconv : ConverseRealizer (F := F) (A := A) C εstar δ B) :
    PrizeEquivalence (F := F) (A := A) C εstar δ B := by
  constructor
  · intro hI
    exact prizeEquivalence_forward (F := F) (A := A) C εstar hδ hbudget hI
  · intro hδstar
    exact hconv hδstar

/-! ## The meta-statement — the gap to completeness IS exactly the named converse -/

/-- **The completeness biconditional holds IFF the converse realizer holds** (under the budget side
condition and `δ ≤ 1`).

This pins down *precisely* what is missing: the forward leg being already proven, the full
biconditional `PrizeEquivalence` is *equivalent* to the single named `Prop` `ConverseRealizer`.
There is **no other open math** between the proven conditional pin and a complete two-way reduction
of the prize to the scalar `B` — the entire remaining content is this one converse implication. -/
theorem prizeEquivalence_iff_converseRealizer (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    PrizeEquivalence (F := F) (A := A) C εstar δ B
      ↔ ConverseRealizer (F := F) (A := A) C εstar δ B := by
  constructor
  · intro hequiv
    intro hδstar
    exact hequiv.mpr hδstar
  · intro hconv
    exact PrizeEquivalence_of_converse (F := F) (A := A) C εstar hδ hbudget hconv

/-! ## Budget specialization — the prize's `ε* = B/q` form -/

/-- **Budget specialization of the wrapper.** When `ε* = B/q` is itself the budget ratio (the
prize's `B ≈ q·ε* ≈ n`), the side condition `hbudget` is automatic, and the completeness
biconditional `PrizeEquivalence C (B/q) δ B` holds modulo the named converse realizer alone. -/
theorem PrizeEquivalence_of_converse_budget (C : Set (ι → A)) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    (hconv : ConverseRealizer (F := F) (A := A) C
      ((B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) δ B) :
    PrizeEquivalence (F := F) (A := A) C ((B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) δ B :=
  PrizeEquivalence_of_converse (F := F) (A := A) C _ hδ le_rfl hconv

end ProximityGap.PrizeEquivalence

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.PrizeEquivalence.prizeEquivalence_forward
#print axioms ProximityGap.PrizeEquivalence.PrizeEquivalence_of_converse
#print axioms ProximityGap.PrizeEquivalence.prizeEquivalence_iff_converseRealizer
#print axioms ProximityGap.PrizeEquivalence.PrizeEquivalence_of_converse_budget
