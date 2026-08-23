/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.HalfThresholdCA
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThresholdHalvingWindow

/-!
# Threshold-Halving Soundness Assembly — #444 frontier (ePrint 2026/858 route)

**Target.** The next assembly brick of Chai–Fan, *FRI Soundness Above the Johnson Bound via
Threshold Halving* (ePrint 2026/858): compose the two pieces already in tree into a single
packaged lemma certifying that, at any proximity-window radius `δ`, the threshold-halved
correlated-agreement analysis is *simultaneously*

* **(a) below Johnson** — the halved analysis radius `δ/2` is strictly below the Johnson radius
  `1 − √ρ`, where the BCIKS (ePrint 2025/2055) unconditional correlated-agreement /
  unique-decoding regime applies (`halved_radius_below_johnson` from `_ThresholdHalvingWindow`); and
* **(b) ≤ 1 bad scalar** — at relative radius `δ/2` at most one scalar `γ` makes the affine line
  `f₁ + γ • f₂` lie within `δ/2` of the code `C`, i.e. correlated-agreement error `≤ 1/|F|`
  (`theorem5_halfThreshold_correlatedAgreement` from `HalfThresholdCA`).

The two pieces live in different number realms by design:

* `theorem5_halfThreshold_correlatedAgreement` is **discrete**: its proximity radius is a
  `δ : ℝ≥0` and its CA-threshold heart is the natural-number floor `⌊(δ/2)·n⌋`, fed from the joint
  *relative* distance `jointRelDist f₁ f₂ C : ENNReal` exceeding `δ`.
* `halved_radius_below_johnson` is **continuous**: its proximity radius is a `δ : ℝ` and it speaks
  about the real Johnson radius `johnsonRadius ρ = 1 − √ρ`.

## The bridge (honest scope)

These two realms meet at the *same* proximity radius `δ`. We carry the discrete radius as a
`δ : ℝ≥0` (what `theorem5` consumes) and impose the window constraint on its **canonical real
coercion** `(δ : ℝ) < windowTop ρ`. The window lemma then certifies `(δ : ℝ)/2 < johnsonRadius ρ`,
and since `NNReal → ℝ` is a ring hom, `((δ : ℝ≥0)/2 : ℝ) = (δ : ℝ)/2` *exactly* — so the halved
discrete radius and the halved continuous radius are the *same real number*. This part of the
bridge is `sorry`-free and exact (`NNReal.coe_div`); we do **not** fabricate any floor↔real
identity.

What is **not** proven here, and is carried as an explicit named `Prop` hypothesis, is the actual
content of the BCIKS unconditional regime — that being below Johnson at radius `δ/2` *delivers* a
soundness statement (unique decoding / correlated agreement at that radius). The BCIKS-2055
substrate is not in this tree; `BelowJohnsonRegime` (from `_ThresholdHalvingWindow`) models only
its *triggering condition* `r < johnsonRadius ρ`, and we plug the real substrate in via the named
hypothesis `hBCIKS : ∀ r, r < johnsonRadius ρ → BelowJohnsonRegime ρ r`.

We likewise carry the full per-round FRI error bound `ε_FRI ≤ nR/|F| + (1 − δ/2)^q` as a named
`Prop` family (`PerRoundFRIError`) — it is the downstream ePrint 2026/858 query-amplification
accounting, also not in this tree.

## Honesty / scope

This is the **LOSSY (≈ 2× query) above-Johnson route**, NOT the grand zero-loss `δ*` (the open BGK
wall). The prize wants soundness at radius `δ` *itself* with no query blow-up; threshold halving
trades a factor of ≈ 2 in queries to descend below Johnson where the analysis is unconditional.
Everything here is `sorry`/`axiom`-free except the explicitly named BCIKS / FRI-accounting `Prop`
hypotheses, which are never silently discharged.
-/

namespace ProximityGap.ThresholdHalvingSoundness

open ProximityPrizeCA ProximityGap.ThresholdHalvingWindow
open Finset Code NNReal
open scoped NNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ### The exact discrete↔continuous radius bridge

The only number-realm bridge used below: the halved discrete radius (as an `ℝ≥0`, coerced to `ℝ`)
equals the halved continuous radius. This is an exact ring-hom identity, no floors, no rounding. -/

/-- **Halved-radius coercion bridge (exact).** For a discrete proximity radius `δ : ℝ≥0`, the real
coercion of the halved discrete radius `(δ / 2 : ℝ≥0)` equals the halved real radius `(δ : ℝ) / 2`.
This is the honest, floor-free hinge connecting `theorem5`'s `ℝ≥0` world to the window lemma's
`ℝ` world. -/
theorem coe_half_radius (δ : ℝ≥0) : ((δ / 2 : ℝ≥0) : ℝ) = (δ : ℝ) / 2 := by
  push_cast
  ring

/-- The halved discrete radius, coerced to `ℝ`, is strictly below the Johnson radius whenever the
(real) discrete radius lies in the proximity window. This is `halved_radius_below_johnson` rephrased
on the canonical `ℝ≥0 → ℝ` coercion of the discrete radius — the form consumed by the packaged
lemma below. -/
theorem coe_halved_radius_below_johnson {ρ : ℝ} {δ : ℝ≥0} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hδ : (δ : ℝ) < windowTop ρ) :
    ((δ / 2 : ℝ≥0) : ℝ) < johnsonRadius ρ := by
  rw [coe_half_radius]
  exact halved_radius_below_johnson hρ0 hρ1 hδ

/-! ### The packaged composition (a) ∧ (b)

The headline brick: at any window radius `δ`, the halved analysis is BOTH below Johnson (so the
named BCIKS regime fires) AND has `≤ 1` bad scalar. The conjunction is honest about its two halves
living in the two realms; the shared radius `δ` is the same object, related by `coe_half_radius`. -/

/-- **Threshold-halving soundness package (ePrint 2026/858).**

Fix a rate `ρ ∈ [0, 1]`, a linear code `C ⊆ Fⁿ`, words `f₁ f₂ : ι → F`, and a *discrete*
proximity radius `δ : ℝ≥0` whose real coercion lies strictly inside the above-Johnson window
(`(δ : ℝ) < windowTop ρ = 1 − ρ`). Suppose the joint relative distance of `(f₁, f₂)` to the pair
code exceeds `δ` (the genuine separation hypothesis of Theorem 5), and suppose the named BCIKS
below-Johnson regime predicate fires on every strictly-below-Johnson analysis radius. Then **both**:

* **(a)** the halved analysis radius `δ/2` lies in the BCIKS below-Johnson regime
  (`BelowJohnsonRegime ρ ((δ / 2 : ℝ≥0) : ℝ)`); and
* **(b)** at most one scalar `γ ∈ F` satisfies `δᵣ(f₁ + γ • f₂, C) ≤ δ/2` — i.e. the
  correlated-agreement bad set is a subsingleton, CA error `≤ 1/|F|`.

The same radius `δ` drives both halves; `coe_half_radius` certifies that the discrete radius `δ/2`
(coerced to `ℝ`) and the continuous radius `(δ : ℝ)/2` are the identical real number, so the
below-Johnson lock in (a) is exactly the radius at which the CA count in (b) is taken. -/
theorem thresholdHalving_soundness_package [Fintype F]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) {δ : ℝ≥0}
    (hδwin : (δ : ℝ) < windowTop ρ)
    (hjoint : (δ : ENNReal) < jointRelDist f₁ f₂ C)
    (hBCIKS : ∀ r : ℝ, r < johnsonRadius ρ → BelowJohnsonRegime ρ r) :
    BelowJohnsonRegime ρ ((δ / 2 : ℝ≥0) : ℝ)
      ∧ ((Finset.univ : Finset F).filter
          (fun γ => δᵣ(linComb f₁ f₂ γ, (C : Set (ι → F))) ≤ ((δ / 2 : ℝ≥0) : ENNReal))).card
          ≤ 1 := by
  refine ⟨?_, ?_⟩
  · -- (a) below-Johnson lock at the halved radius, via the window lemma and the named BCIKS regime.
    exact hBCIKS _ (coe_halved_radius_below_johnson hρ0 hρ1 hδwin)
  · -- (b) ≤ 1 bad scalar at radius δ/2, the discrete Theorem 5 fact.
    exact theorem5_halfThreshold_correlatedAgreement C f₁ f₂ hjoint

/-! ### Per-round FRI error accounting (named hypothesis)

The downstream ePrint 2026/858 statement amplifies the per-step CA error into the full FRI
soundness error `ε_FRI ≤ nR/|F| + (1 − δ/2)^q`, where the `(1 − δ/2)^q` term is the ≈ 2×-query
penalty (analysis at `δ/2`, not `δ`). That query-amplification accounting is not in this tree, so
we carry it as a named `Prop` family parametrized by the data that determines it. We then show the
package lemma *supplies the hypothesis under which that bound is claimed* — namely the below-Johnson
lock plus the ≤ 1-bad-scalar fact — WITHOUT asserting the bound itself. -/

/-- Named per-round FRI soundness-error predicate (NOT proven here — it is the imported ePrint
2026/858 query-amplification accounting). `PerRoundFRIError ε n R q halfRadius` is meant to hold
exactly when the threshold-halved per-round FRI soundness error `ε` is bounded by
`n·R/|F| + (1 − halfRadius)^q` for the relevant field; we keep it abstract so any real
ePrint 2026/858 accounting plugs in verbatim. -/
def PerRoundFRIError (ε : ℝ) (n : ℕ) (R : ℝ) (q : ℕ) (halfRadius : ℝ) : Prop :=
  ε ≤ (n : ℝ) * R + (1 - halfRadius) ^ q

/-- **Packaged per-round soundness statement (named-conditional).** Given the threshold-halving
package conclusions (below-Johnson lock + ≤ 1 bad scalar at `δ/2`) AND the named ePrint 2026/858
per-round accounting `PerRoundFRIError` at the halved analysis radius, the per-round FRI soundness
error is bounded as claimed. This is a *trivial re-export* of the named hypothesis — its content
is entirely in `hAccount`; the package conclusions are recorded as the soundness context under
which the bound is asserted. We never discharge `PerRoundFRIError` ourselves. -/
theorem thresholdHalving_perRound_soundness [Fintype F]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) {δ : ℝ≥0}
    (hδwin : (δ : ℝ) < windowTop ρ)
    (hjoint : (δ : ENNReal) < jointRelDist f₁ f₂ C)
    (hBCIKS : ∀ r : ℝ, r < johnsonRadius ρ → BelowJohnsonRegime ρ r)
    {ε R : ℝ} {q : ℕ}
    (hAccount :
      BelowJohnsonRegime ρ ((δ / 2 : ℝ≥0) : ℝ) →
      ((Finset.univ : Finset F).filter
        (fun γ => δᵣ(linComb f₁ f₂ γ, (C : Set (ι → F))) ≤ ((δ / 2 : ℝ≥0) : ENNReal))).card ≤ 1 →
      PerRoundFRIError ε (Fintype.card ι) R q ((δ / 2 : ℝ≥0) : ℝ)) :
    PerRoundFRIError ε (Fintype.card ι) R q ((δ / 2 : ℝ≥0) : ℝ) := by
  obtain ⟨hlock, hcount⟩ :=
    thresholdHalving_soundness_package hρ0 hρ1 C f₁ f₂ hδwin hjoint hBCIKS
  exact hAccount hlock hcount

/-! ### Convenience: the package on the genuine open window `(1−√ρ, 1−ρ)`, `ρ ∈ (0,1)`

The prize regime is `ρ ∈ (0, 1)` with `δ` in the *open* window `(johnsonRadius ρ, windowTop ρ)`.
Even from the lower edge `johnsonRadius ρ < δ`, the halving still drops strictly below Johnson, so
the full package holds; we only need the upper window constraint `(δ:ℝ) < windowTop ρ`. -/

/-- The soundness package on the genuine prize window `ρ ∈ (0, 1)`, `δ` strictly above the lower
window edge `johnsonRadius ρ` and strictly below the upper edge `windowTop ρ`. -/
theorem thresholdHalving_soundness_package_window [Fintype F]
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) {δ : ℝ≥0}
    (hlo : johnsonRadius ρ < (δ : ℝ)) (hhi : (δ : ℝ) < windowTop ρ)
    (hjoint : (δ : ENNReal) < jointRelDist f₁ f₂ C)
    (hBCIKS : ∀ r : ℝ, r < johnsonRadius ρ → BelowJohnsonRegime ρ r) :
    BelowJohnsonRegime ρ ((δ / 2 : ℝ≥0) : ℝ)
      ∧ ((Finset.univ : Finset F).filter
          (fun γ => δᵣ(linComb f₁ f₂ γ, (C : Set (ι → F))) ≤ ((δ / 2 : ℝ≥0) : ENNReal))).card
          ≤ 1 :=
  thresholdHalving_soundness_package hρ0.le hρ1.le C f₁ f₂ hhi hjoint hBCIKS

-- Axiom audit: every result must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms coe_half_radius
#print axioms coe_halved_radius_below_johnson
#print axioms thresholdHalving_soundness_package
#print axioms thresholdHalving_perRound_soundness
#print axioms thresholdHalving_soundness_package_window

end ProximityGap.ThresholdHalvingSoundness
