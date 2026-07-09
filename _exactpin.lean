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
`mcaDeltaStar` brackets that **meet**" — one needs the two-sided combinator that produces an
equality `δ* = δ₀` from a good point at `δ₀` together with badness strictly above it.

This file supplies that missing piece, `mcaDeltaStar_eq_of_good_of_bad_above`, plus the
convenient `bad_above` packaging. Every exact `δ*` pin (toy instances now, the eventual
explicit smooth-RS pin later) routes through it.

**Empirical anchor (probe-verified, cross-checked two ways, witness-disciplined; see
`scripts/probes/probe_exact_pin.py` and the dossier `docs/wiki/fable-deltastar-attack-2026-06.md`):**
for `RS[F₁₃, D, 2]` (`n = 4`), `ε_mca = 1/13` for `δ < 1/4` and `= 4/13` for `δ ≥ 1/4`, the jump
sitting exactly at the unique-decoding radius `(1−ρ)/2 = 1/4`. Hence for any `ε* ∈ [1/13, 4/13)`,
`δ*(RS[F₁₃,D,2], ε*) = 1/4` — the *first exact δ\* value for any code* (the dossier records none
exist anywhere). Its Lean discharge (the exact `epsMCA` computation for that concrete code) is the
remaining ingredient; this combinator is the bracket-meet half, proven now.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

open scoped NNReal ENNReal
open ProximityGap

namespace ProximityGap.MCAThresholdLedger

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The exact-pin combinator.** If `δ₀ ≤ 1` is a *good* radius (`ε_mca(C, δ₀) ≤ ε*`) and
*every strictly larger* radius is *bad* (`ε* < ε_mca(C, δ)` for all `δ > δ₀`), then the formal
threshold is pinned exactly: `δ*(C, ε*) = δ₀`. This is the two-sided "brackets meet" statement —
the grand-challenge target shape. -/
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

/-- Convenience repackaging: the "bad above" hypothesis from a single monotone bad threshold.
If `δ₀` is good and there is a *bad radius arbitrarily close above* — concretely, every
`δ > δ₀` is bad — the pin holds. (Same content; named for the consumer that supplies a
bad-point family.) -/
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
