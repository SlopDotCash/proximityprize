/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingRefutation

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
  (`OpenCoreConditionalPin`), an integer incidence budget `B`. It is *hoped* to be controlled
  by the Gauss-period sup-norm, i.e. at a budget `B ≈ q·ε* ≈ n` by `‖η_b‖ ≤ C√(n log m)`. No
  in-tree theorem proves that dictionary. `IncidencePeriodBridge.lineIncidence_period_sum` is
  only a one-dimensional `V = F` model, where the incidence is `|G|` for every nonzero direction
  and only `η₀` survives. It is not the syndrome-ball incidence in the `(n − k)`-dimensional
  quotient, so the integer budget `B` here is not automatically the real period norm.

## The completeness biconditional

`PrizeEquivalence C εstar δ B` is the `Prop`

  `WorstCaseIncidenceBounded C δ B  ↔  δ ≤ mcaDeltaStar C εstar`

stated at a budget `B/q ≤ ε*` (`hbudget`).  This is the formal object "the prize is EXACTLY the
single scalar `B`": a proven two-way reduction between the `δ*` window pin and the open core.

* **Forward direction** (`B`-side ⟹ `δ*`-side): **PROVEN, axiom-clean** — this is
  `OpenCoreConditionalPin.worstCaseIncidence_pin`. A bound on the worst-case incidence `B` forces
  the `δ*` lower pin.

* **Converse direction** (`δ*`-side ⟹ `B`-side): stated here as the named `Prop`
  `ConverseRealizer C εstar δ B`. **As a generic target it is REFUTED**
  (`converseRealizer_refuted`): over `F₂` on one coordinate with `C = {0}`, the stack `(0, 1)`
  has the bad scalar `0` at radius `0`, so at `εstar = 0`, `δ = 0`, `B = 0` the budget holds with
  equality (`B/q = εstar`) and `δ ≤ mcaDeltaStar` holds trivially (the good-radius set is empty
  and its `ℝ≥0` supremum is `0`), yet `WorstCaseIncidenceBounded C 0 0` fails. The closed
  endpoint `δ ≤ δ*` at an unattained supremum cannot force the incidence bound, and with slack
  `B/q < εstar` an interior good radius need not force the smaller integer budget `B` either. A
  correct converse would have to be formulated at strict radius `δ < δ*` with a matching integer
  probability budget (cf. the PG-027 endpoint family); none is proved here. `ConverseRealizer` is
  therefore only an instance-level hypothesis, false for some `(C, εstar, δ, B)`.

## What is proven (axiom-clean, no `sorry`)

* `PrizeEquivalence_of_converse` — the **wrapper theorem**: given the converse realizer
  `ConverseRealizer` (named) and the budget side condition `hbudget`, the full biconditional
  `PrizeEquivalence` holds. The forward leg is discharged outright by `worstCaseIncidence_pin`;
  only the converse leg consumes the named hypothesis.

* `prizeEquivalence_forward` — the forward leg, fully proven and standalone (= the open-core pin).

* `prizeEquivalence_iff_converseRealizer` — meta-statement: under the budget side condition, the
  biconditional `PrizeEquivalence` holds **iff** the converse realizer holds (for the given
  instance). Since the converse realizer is refuted at some instances, so is the biconditional.

* `converseRealizer_refuted` — the checked counterexample above: `ConverseRealizer` and
  `PrizeEquivalence` both fail at `F₂`, `C = {0}`, `εstar = 0`, `δ = 0`, `B = 0`, although every
  side condition of the wrapper (`δ ≤ 1`, `B/q ≤ εstar`) holds.

## Honest scope (the load-bearing self-check)

* **Direction proven: forward only.** The forward `B ⟹ δ*` is proven (the open-core conditional
  pin). The converse `δ* ⟹ B` is **not** a valid generic statement (`converseRealizer_refuted`);
  the biconditional is only `proven modulo ConverseRealizer` at instances where that hypothesis
  happens to hold, and the advertised "prize = exactly the scalar `B`" equivalence is not
  established. Moreover the integer incidence budget `B` here is not automatically the real
  Gauss-period sup-norm `max_{b≠0} ‖η_b‖` of the introduction; relating them needs a separate
  bridge (audit PG-070). The `B`-side itself (`WorstCaseIncidenceBounded` at window budget, i.e.
  `B ≤ C√(n log m)`) remains the recognized open BGK/Paley wall — NOT closed here.
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

/-- **The converse realizer (`δ*`-side ⟹ `B`-side), as a named instance-level `Prop`.**

The converse direction of the would-be completeness biconditional: *if* the threshold reaches
the window radius `δ ≤ mcaDeltaStar C εstar`, *then* the worst-case far-line incidence is
bounded, `WorstCaseIncidenceBounded C δ B`.

**Refuted as a generic target** (`converseRealizer_refuted`): at `F₂`, one coordinate, `C = {0}`,
`εstar = 0`, `δ = 0`, `B = 0` the budget `B/q ≤ εstar` holds with equality and `δ ≤ δ*` holds
(the good-radius set is empty, its supremum is `0`), but the stack `(0, 1)` has a bad scalar.
The closed endpoint at an unattained supremum, and any slack `B/q < εstar`, break the
implication. A usable converse needs a strict radius `δ < δ*` and a matching integer budget; it
is not stated or proved here. -/
def ConverseRealizer (C : Set (ι → A)) (εstar : ℝ≥0∞) (δ : ℝ≥0) (B : ℕ) : Prop :=
  δ ≤ mcaDeltaStar (F := F) (A := A) C εstar →
    WorstCaseIncidenceBounded (F := F) (A := A) C δ B

/-! ## The completeness biconditional -/

/-- **THE PRIZE COMPLETENESS STATEMENT (`δ*` ⟺ the single scalar `B`).**

`PrizeEquivalence C εstar δ B` is the biconditional

  `WorstCaseIncidenceBounded C δ B  ↔  δ ≤ mcaDeltaStar C εstar`.

It is the *proposed* statement that, at the window radius `δ` and budget `B`, the prize "δ*
reaches the window" statement is logically equivalent to the far-line incidence bound `B`. It is
NOT valid in general: it fails at the instance of `converseRealizer_refuted`, where all side
conditions of the wrapper hold. -/
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

The wrapper is a valid conditional theorem, but its hypothesis `hconv` is false at some
instances satisfying (a) and (b) (`converseRealizer_refuted`), so it does not show that the prize
is exactly the scalar `B`. -/
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

The forward leg being proven, the biconditional `PrizeEquivalence` is equivalent (instance by
instance) to `ConverseRealizer`. Because `ConverseRealizer` is refuted at some instances
(`converseRealizer_refuted`), this does not reduce the prize to a hard-but-open converse: the
generic converse is false, and a corrected strict-radius formulation would be needed. -/
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
prize's `B ≈ q·ε* ≈ n`), the side condition `hbudget` is automatic, and the biconditional
`PrizeEquivalence C (B/q) δ B` holds modulo the converse realizer at that instance. (The
refutation `converseRealizer_refuted` is itself of this exact-budget form, `0 = 0/2`.) -/
theorem PrizeEquivalence_of_converse_budget (C : Set (ι → A)) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    (hconv : ConverseRealizer (F := F) (A := A) C
      ((B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) δ B) :
    PrizeEquivalence (F := F) (A := A) C ((B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) δ B :=
  PrizeEquivalence_of_converse (F := F) (A := A) C _ hδ le_rfl hconv

end ProximityGap.PrizeEquivalence

/-! ## The converse realizer is refuted at an unattained-supremum endpoint -/

namespace ProximityGap.PrizeEquivalence

open CodingTheory.LineDecodingRefutation in
/-- **`ConverseRealizer` (and hence `PrizeEquivalence`) is false as a generic target.**  Over
`F₂` on one coordinate with `C = {0}`, at `εstar = 0`, `δ = 0`, `B = 0`: the wrapper's side
conditions hold (`δ ≤ 1`, and `B/q = 0 ≤ εstar` with equality), `δ = 0 ≤ mcaDeltaStar C 0`
trivially, yet the stack `(0, 1)` has the bad scalar `0` (`mcaEvent_ubad_zero`), so the worst
bad count is `≥ 1 > B`.  Hence both `ConverseRealizer C 0 0 0` and `PrizeEquivalence C 0 0 0`
fail. -/
theorem converseRealizer_refuted :
    (0 : ℝ≥0) ≤ 1 ∧
      ((0 : ℕ) : ℝ≥0∞) / (Fintype.card (ZMod 2) : ℝ≥0∞) ≤ 0 ∧
      ¬ ConverseRealizer (F := ZMod 2) (A := ZMod 2)
          ((Czero : Submodule (ZMod 2) (Fin 1 → ZMod 2)) : Set (Fin 1 → ZMod 2)) 0 0 0 ∧
      ¬ PrizeEquivalence (F := ZMod 2) (A := ZMod 2)
          ((Czero : Submodule (ZMod 2) (Fin 1 → ZMod 2)) : Set (Fin 1 → ZMod 2)) 0 0 0 := by
  classical
  have hbad : ¬ WorstCaseIncidenceBounded (F := ZMod 2) (A := ZMod 2)
      ((Czero : Submodule (ZMod 2) (Fin 1 → ZMod 2)) : Set (Fin 1 → ZMod 2)) 0 0 := by
    intro h
    have hle := h ubad
    have hpos : 0 < (Finset.univ.filter (fun γ : ZMod 2 => mcaEvent (F := ZMod 2)
        ((Czero : Submodule (ZMod 2) (Fin 1 → ZMod 2)) : Set (Fin 1 → ZMod 2)) 0
        (ubad 0) (ubad 1) γ)).card :=
      Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_ubad_zero⟩⟩
    omega
  refine ⟨zero_le_one, by simp, ?_, ?_⟩
  · intro hconv
    exact hbad (hconv (zero_le _))
  · intro hequiv
    exact hbad (hequiv.mpr (zero_le _))

end ProximityGap.PrizeEquivalence

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.PrizeEquivalence.prizeEquivalence_forward
#print axioms ProximityGap.PrizeEquivalence.PrizeEquivalence_of_converse
#print axioms ProximityGap.PrizeEquivalence.prizeEquivalence_iff_converseRealizer
#print axioms ProximityGap.PrizeEquivalence.PrizeEquivalence_of_converse_budget
#print axioms ProximityGap.PrizeEquivalence.converseRealizer_refuted
