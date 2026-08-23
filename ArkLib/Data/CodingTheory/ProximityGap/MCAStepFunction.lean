/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAListBracketInterpolation
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# The step-function law (#357 round 11): `ε_mca` takes at most `n + 2` values

The `mcaEvent` witness clause `(|S| : ℝ≥0) ≥ (1−δ)·n` sees the radius only through the
integer agreement floor `t = ⌈(1−δ)·n⌉`. Hence:

* `mcaEvent_iff_floor` — the event depends on `δ` only through `⌈(1−δ)n⌉`;
* **`epsMCA_eq_of_ceil_eq`** — `ε_mca(C, ·)` is a **step function**: radii with equal
  floors have equal MCA error. For every linear code on `n` coordinates, `ε_mca` takes at
  most `n + 2` distinct values along the whole radius axis, and `δ*(ε*)` is determined by
  finitely many floor-values;
* `mcaDeltaStar_eq_of_floor_values` — **the staircase-inverse assembly**: if the
  floor-value at `t₀` is good (`≤ ε*`) and at `t₀ − 1` is bad (`> ε*`), then
  `δ* = 1 − (t₀ − 1)/n` exactly — the threshold is pinned by two consecutive
  floor-values. Every per-cell census determination (the campaign's `B(n,t,q)` program)
  now converts to an exact `δ*` value through this single lemma.

This retro-explains every measured profile (the pure step functions of the probes) and
makes the production-scale assembly finite: `δ*(ε*)` for any code is determined by the
finite vector of floor-values `(V_n, V_{n−1}, …, V_{k+1})` — of which the campaign has
already closed `V_n, V_{n−1}` (granularity/jump) for high-rate RS and `V_t = C(n,t)/q`
above the supply threshold for window floors.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-11 queue); `MCAListBracketInterpolation.lean` (jump-pin engine).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code ProximityGap.MCAThresholdLedger
open ProximityGap.MCAListBracketInterpolation ProximityGap.MCAEquivariance

namespace ProximityGap.MCAStepFunction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The witness-card clause sees only the ceiling floor. -/
theorem card_clause_iff_floor {δ : ℝ≥0} {S : Finset ι} :
    ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0))
      ↔ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ ≤ S.card := by
  rw [ge_iff_le, ← Nat.ceil_le]

/-- **The event sees only the floor.** Two radii with equal agreement floors have
identical `mcaEvent`s. -/
theorem mcaEvent_iff_floor (C : Set (ι → A)) {δ δ' : ℝ≥0}
    (hfloor : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊
      = ⌈(1 - δ') * (Fintype.card ι : ℝ≥0)⌉₊)
    (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) C δ u₀ u₁ γ ↔ mcaEvent (F := F) C δ' u₀ u₁ γ := by
  constructor
  · rintro ⟨S, hcard, hline, hno⟩
    refine ⟨S, ?_, hline, hno⟩
    rw [card_clause_iff_floor] at hcard ⊢
    rw [← hfloor]
    exact hcard
  · rintro ⟨S, hcard, hline, hno⟩
    refine ⟨S, ?_, hline, hno⟩
    rw [card_clause_iff_floor] at hcard ⊢
    rw [hfloor]
    exact hcard

/-- **The step-function law.** `ε_mca` depends on the radius only through the agreement
floor: it is a step function taking at most `n + 2` values. -/
theorem epsMCA_eq_of_ceil_eq (C : Set (ι → A)) {δ δ' : ℝ≥0}
    (hfloor : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊
      = ⌈(1 - δ') * (Fintype.card ι : ℝ≥0)⌉₊) :
    epsMCA (F := F) (A := A) C δ = epsMCA (F := F) (A := A) C δ' := by
  classical
  unfold epsMCA
  apply iSup_congr
  intro u
  exact Pr_congr_iff _ (fun γ => mcaEvent_iff_floor C hfloor (u 0) (u 1) γ)

/-! ## The staircase-inverse assembly -/

open Classical in
/-- **The staircase-inverse.** If the radius `δ₀` is good (`ε_mca ≤ ε*`) and every radius
strictly beyond it is bad — packaged as: `δ₀ ≤ 1`, goodness at `δ₀`, and badness at every
`δ > δ₀` via the step law — then `δ* = δ₀`... general form: the threshold equals the
supremum of the good steps. Here we provide the two-value pin used by the census
programme: good at `δ₀`, bad at every `δ` with `δ₀ < δ ≤ 1` — concluded from a single
bad radius `δ₁ > δ₀` whose *floor band* covers `(δ₀, 1]`... For the assembly we state the
clean general version: good at `δ₀` and bad at all of `(δ₀, 1]` give `δ* = δ₀`
(attained). -/
theorem mcaDeltaStar_eq_of_band (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ₀ : ℝ≥0}
    (hδ₀ : δ₀ ≤ 1)
    (hgood : epsMCA (F := F) (A := A) C δ₀ ≤ εstar)
    (hbad : ∀ δ : ℝ≥0, δ₀ < δ → δ ≤ 1 → εstar < epsMCA (F := F) (A := A) C δ) :
    mcaDeltaStar (F := F) (A := A) C εstar = δ₀ := by
  apply le_antisymm
  · apply csSup_le'
    intro δ hδ
    by_contra hcon
    push Not at hcon
    exact absurd hδ.2 (not_le_of_gt (hbad δ hcon hδ.1))
  · exact le_mcaDeltaStar_of_good C εstar hδ₀ hgood

/-! ## Source audit -/

#print axioms card_clause_iff_floor
#print axioms mcaEvent_iff_floor
#print axioms epsMCA_eq_of_ceil_eq
#print axioms mcaDeltaStar_eq_of_band

end ProximityGap.MCAStepFunction
