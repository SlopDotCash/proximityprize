/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The exact-pin combinator for `δ*` (#357)

The bracket engine (`MCAThresholdLedger.lean`) ships the two *one-sided* brackets
`le_mcaDeltaStar_of_good` (a good point lies below `δ*`) and `mcaDeltaStar_le_of_bad` (a bad
point lies above `δ*`). To *pin* `δ*` to an exact value — the grand-challenge target, "two
`mcaDeltaStar` brackets that **meet**" — one needs a two-sided combinator that produces an
equality `δ* = δ₀`.

The usable form is **`mcaDeltaStar_eq_of_good_below_of_bad_above`**: goodness at every radius
strictly below `δ₀` and badness at every radius `≥ δ₀` give `δ* = δ₀`, with `δ₀` itself bad.
The in-tree exact pins use this shape (or the equivalent jump pin
`MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump`): `ε_mca` sees the radius only through the
agreement floor `⌈(1 − δ)·n⌉₊` (`MCAStepFunction.epsMCA_eq_of_ceil_eq`), whose cells are open on
the right, so a threshold `δ* < 1` is never itself a good radius
(`MCAStepFunction.lt_epsMCA_mcaDeltaStar_of_lt_one`).

**Correction (audit 2026-10-28, PG-027).** An earlier version of this header presented the
closed-good combinator `mcaDeltaStar_eq_of_good_of_bad_above` (goodness **at** `δ₀`, badness at
every `δ > δ₀`) as the missing piece through which every exact pin routes. That implication is
valid, but its premises are never jointly satisfiable for the repository's `ε_mca`
(`MCAStepFunction.not_good_and_bad_above`), so it pins no threshold; the same holds for its alias
`mcaDeltaStar_eq_of_good_of_strictMono_bad`, which has identical hypotheses and conclusion.

**Empirical anchor (probe-verified, cross-checked two ways, witness-disciplined; see
`scripts/probes/probe_exact_pin.py` and the dossier `docs/wiki/fable-deltastar-attack-2026-06.md`):**
for `RS[F₁₃, D, 2]` (`n = 4`), `ε_mca = 1/13` for `δ < 1/4` and `= 4/13` for `δ ≥ 1/4`, the jump
sitting exactly at the unique-decoding radius `(1−ρ)/2 = 1/4`. Hence for any `ε* ∈ [1/13, 4/13)`,
`δ*(RS[F₁₃,D,2], ε*) = 1/4` — the *first exact δ\* value for any code* (the dossier records none
exist anywhere). Its Lean discharge (the exact `epsMCA` computation for that concrete code) is the
remaining ingredient; the good-below/bad-at-and-above combinator is the bracket-meet half,
proven now.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

open scoped NNReal ENNReal
open ProximityGap

namespace ProximityGap.MCAThresholdLedger

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Closed-good pin (vacuous premises).** If `δ₀ ≤ 1` is a *good* radius
(`ε_mca(C, δ₀) ≤ ε*`) and *every strictly larger* radius is *bad* (`ε* < ε_mca(C, δ)` for all
`δ > δ₀`), then `δ*(C, ε*) = δ₀`. The implication is valid, but for the repository's `ε_mca` the
premises are never jointly satisfiable: every radius has a strictly larger radius with the same
agreement floor and hence the same MCA error (`MCAStepFunction.not_good_and_bad_above`; audit
2026-10-28, PG-027). It therefore pins no threshold; exact pins use
`mcaDeltaStar_eq_of_good_below_of_bad_above` (goodness below `δ₀`, badness at and above it). -/
theorem mcaDeltaStar_eq_of_good_of_bad_above
    (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ₀ : ℝ≥0}
    (hδ₀ : δ₀ ≤ 1)
    (hgood : epsMCA (F := F) (A := A) C δ₀ ≤ εstar)
    (hbad : ∀ δ : ℝ≥0, δ₀ < δ → εstar < epsMCA (F := F) (A := A) C δ) :
    mcaDeltaStar (F := F) (A := A) C εstar = δ₀ := by
  refine le_antisymm ?_ (le_mcaDeltaStar_of_good (F := F) (A := A) C εstar hδ₀ hgood)
  -- every good radius lies `≤ δ₀` (anything above is bad), so `δ₀` upper-bounds the good set
  refine csSup_le' (show δ₀ ∈ upperBounds (mcaGoodRadii (F := F) (A := A) C εstar) from ?_)
  intro δ hδ
  by_contra hnot
  exact absurd hδ.2 (not_le_of_gt (hbad δ (lt_of_not_ge hnot)))

/-- Alias of `mcaDeltaStar_eq_of_good_of_bad_above`, with identical hypotheses (goodness at
`δ₀`, badness at every `δ > δ₀`) and conclusion; it adds no guarantee. Its premises are likewise
never jointly satisfiable for the repository's `ε_mca`
(`MCAStepFunction.not_good_and_bad_above`). -/
theorem mcaDeltaStar_eq_of_good_of_strictMono_bad
    (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ₀ : ℝ≥0}
    (hδ₀ : δ₀ ≤ 1)
    (hgood : epsMCA (F := F) (A := A) C δ₀ ≤ εstar)
    (hbad : ∀ δ : ℝ≥0, δ₀ < δ → εstar < epsMCA (F := F) (A := A) C δ) :
    mcaDeltaStar (F := F) (A := A) C εstar = δ₀ :=
  mcaDeltaStar_eq_of_good_of_bad_above C εstar hδ₀ hgood hbad

/-- **The open-interval exact-pin combinator.** If *every* radius *strictly below* `δ₀` is good
(`ε_mca(C, δ) ≤ ε*`) and *every* radius *at or above* `δ₀` is bad (`ε* < ε_mca(C, δ)`), then
`δ*(C, ε*) = δ₀` — even though `δ₀` itself is **bad** (the good set is the open interval
`[0, δ₀)`, whose supremum is `δ₀`). This is the form an exact pin takes when `ε_mca` *jumps
across* `ε*` exactly at `δ₀` (a granularity boundary): the pin sits at the jump point. -/
theorem mcaDeltaStar_eq_of_good_below_of_bad_above
    (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ₀ : ℝ≥0}
    (hδ₀ : δ₀ ≤ 1)
    (hgood : ∀ δ : ℝ≥0, δ < δ₀ → epsMCA (F := F) (A := A) C δ ≤ εstar)
    (hbad : ∀ δ : ℝ≥0, δ₀ ≤ δ → εstar < epsMCA (F := F) (A := A) C δ) :
    mcaDeltaStar (F := F) (A := A) C εstar = δ₀ := by
  refine le_antisymm ?_ ?_
  · -- good ⊆ [0, δ₀): any good δ has δ < δ₀ (δ ≥ δ₀ would be bad), so δ₀ upper-bounds good
    refine csSup_le' (show δ₀ ∈ upperBounds (mcaGoodRadii (F := F) (A := A) C εstar) from ?_)
    intro δ hδ
    by_contra hnot
    exact absurd hδ.2 (not_le_of_gt (hbad δ (le_of_lt (not_le.mp hnot))))
  · -- δ₀ ≤ sSup good: if not, pick δ ∈ (sSup, δ₀); δ is good so δ ≤ sSup, contradiction
    by_contra hnot
    rw [not_le] at hnot
    obtain ⟨δ, hδlo, hδhi⟩ := exists_between hnot
    have hδ_good : δ ∈ mcaGoodRadii (F := F) (A := A) C εstar :=
      ⟨le_of_lt (lt_of_lt_of_le hδhi hδ₀), hgood δ hδhi⟩
    exact absurd (le_csSup (mcaGoodRadii_bddAbove (F := F) (A := A) C εstar) hδ_good)
      (not_le_of_gt hδlo)

/-- **Sanity instance (engine self-test): `δ* = 0` when every radius is bad.** If
`ε_mca(C, δ) > ε*` for all `δ`, the good-radius set is empty, so the threshold pins at `0`
(`sSup ∅ = 0`). This is the degenerate exact pin (e.g. the constant code below capacity). -/
theorem mcaDeltaStar_eq_zero_of_all_bad
    (C : Set (ι → A)) (εstar : ℝ≥0∞)
    (hbad : ∀ δ : ℝ≥0, εstar < epsMCA (F := F) (A := A) C δ) :
    mcaDeltaStar (F := F) (A := A) C εstar = 0 := by
  have hempty : mcaGoodRadii (F := F) (A := A) C εstar = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro δ hδ
    exact absurd hδ.2 (not_le_of_gt (hbad δ))
  unfold mcaDeltaStar
  rw [hempty]; simp


end ProximityGap.MCAThresholdLedger

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.MCAThresholdLedger.mcaDeltaStar_eq_of_good_of_bad_above
#print axioms ProximityGap.MCAThresholdLedger.mcaDeltaStar_eq_zero_of_all_bad
#print axioms ProximityGap.MCAThresholdLedger.mcaDeltaStar_eq_of_good_below_of_bad_above
