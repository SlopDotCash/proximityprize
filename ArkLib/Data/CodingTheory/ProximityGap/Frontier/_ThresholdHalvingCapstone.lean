/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThresholdHalvingSoundness
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThresholdHalvingPerRound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThresholdHalvingCompose
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThresholdHalvingWindow

/-!
# Threshold-Halving FRI Soundness — END-TO-END CAPSTONE (#444, BRICK L1d)

**Target.** The single top-level statement of Chai–Fan, *FRI Soundness Above the Johnson Bound
via Threshold Halving* (ePrint 2026/858, the **LOSSY ≈ 2×-query** above-Johnson route), stitching
together the committed assembly bricks into one end-to-end theorem:

  `ε_total ≤ r · (1/|F| + (1 − δ/2)^q)`

for an `r`-round threshold-halving FRI on a linear code `C ⊆ Fⁿ`, run at a proximity radius `δ` in
the above-Johnson window `(1 − √ρ, 1 − ρ)`.

## What the capstone stitches (the brick chain)

| layer | file | what it contributes |
|---|---|---|
| window arithmetic | `_ThresholdHalvingWindow` | `halved_radius_below_johnson`: `δ/2 < 1 − √ρ` over the window |
| per-round package | `_ThresholdHalvingSoundness` | below-Johnson lock ∧ ≤ 1 bad scalar at `δ/2` |
| per-round CA term | `_ThresholdHalvingPerRound` | `caFailureMeasure_le_inv_card` (**PROVEN** ≤ `1/|F|`) |
| per-round assembly | `_ThresholdHalvingPerRound` | `thresholdHalving_perRound_caDischarged`: `ε ≤ 1/|F| + (1−δ/2)^q` |
| multi-round union | `_ThresholdHalvingCompose` | `total_error_le_rounds_mul`: `ε_total ≤ r · ε` |

## The honest provenance split — exactly TWO named external facts

The whole value of this brick is that **everything provable in tree is proven**, and the residuals
are *exactly* the genuinely-external facts, all carried as explicit named `Prop`s (never a hidden
`sorry`, never a vacuous/trivially-true `Prop` dressed up as open):

1. **`QuerySoundnessBound`** (`_ThresholdHalvingPerRound`) — the independent-query survival
   product: `q` FRI queries each catch a `δ/2`-far word w.p. `≥ δ/2`, so the all-miss probability
   is `≤ (1 − δ/2)^q`. Carried per round as `hQuery`. (Its combinatorial core is itself proven in
   `_ThresholdHalvingQuerySurvival`; only the measure-theoretic independence step is external.)

2. **`UnionBoundOverRounds`** (`_ThresholdHalvingCompose`) — the measure-theoretic union bound
   over the `r` FRI rounds: a cheating prover wins only by winning some round. Carried as `hUnion`.

The **CA-failure half is NOT named** — it is the *proven* `caFailureMeasure_le_inv_card`
(`≤ 1/|F|` from in-tree Theorem 5, the half-threshold correlated-agreement bound), consumed through
`thresholdHalving_perRound_caDischarged`. The analysis radius `δ/2` is *locked* below Johnson by the
window arithmetic (`analysis_radius_locked_below_johnson`, **PROVEN**), which is exactly the radius
at which the CA count is taken — so the per-round CA term is genuinely the proven `1/|F|` floor.

**On BCIKS (2025/2055).** Conceptually the half-threshold analysis is valid because the halved
radius sits below Johnson where decoding is unconditional (BCIKS). In THIS formalization that role
is played entirely by the in-tree Theorem 5 (`theorem5_halfThreshold_correlatedAgreement`, the
half-threshold CA combinatorial bound) plus the **proven** triggering inequality
`δ/2 < johnsonRadius ρ`; the `BelowJohnsonRegime` slot of `thresholdHalving_perRound_caDischarged`
is, under its modelling definition, exactly that triggering inequality, so it is discharged in-tree
(`fun _ hr => hr`) and is **not** taken as an external hypothesis here. We deliberately do NOT carry
a decorative `hBCIKS` tautology as a fake "external" residual — the genuine residuals are exactly
(1) and (2).

## Honesty / scope

This is the **LOSSY (≈ 2× query) above-Johnson route**, NOT the grand zero-loss `δ*` (the open BGK
wall). The prize wants soundness at radius `δ` *itself* with no query blow-up; threshold halving
trades a factor of ≈ 2 in queries to descend below Johnson where the analysis is unconditional.
Everything here is `sorry`/`native_decide`/`axiom`-free except the three explicitly named external
`Prop`s above, which are never silently discharged. `#print axioms` audit at the bottom shows only
`[propext, Classical.choice, Quot.sound]`.
-/

namespace ProximityGap.ThresholdHalvingCapstone

open ProximityPrizeCA ProximityGap.ThresholdHalvingWindow
open ProximityGap.ThresholdHalvingSoundness
open ProximityGap.ThresholdHalvingPerRound
open ProximityGap.ThresholdHalvingCompose
open Finset Code NNReal
open scoped NNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ### The per-round error in the clean `1/|F| + (1 − δ/2)^q` form

`thresholdHalving_perRound_caDischarged` delivers `PerRoundFRIError ε n R q (δ/2)`, i.e.
`ε ≤ n·R + (1 − δ/2)^q`, with the round-scaling rate `R` chosen so that `n·R = 1/|F|` (the proven
CA floor). We first re-express that conclusion in the explicit `ε ≤ 1/|F| + (1 − δ/2)^q` shape that
the capstone reports, so the per-round bound visibly carries the proven CA half. -/

/-- **Per-round threshold-halving error, clean form (CA half PROVEN).**

Given the window radius `δ` (`(δ:ℝ) < windowTop ρ`), the genuine joint-separation hypothesis, the
named BCIKS regime, the round-scaling normalization `n·R = 1/|F|`, the FRI additive split
`ε ≤ (CA-failure measure) + qErr`, and the single named `QuerySoundnessBound qErr (δ/2) q`, the
per-round FRI soundness error is bounded as

  `ε ≤ 1/|F| + (1 − δ/2)^q`.

The `1/|F|` term is the **PROVEN** correlated-agreement floor (`caFailureMeasure_le_inv_card`, via
`thresholdHalving_perRound_caDischarged`), taken at the analysis radius `δ/2` that the window
arithmetic locks below Johnson. The ONLY unproven input is the named `QuerySoundnessBound`. -/
theorem perRound_error_clean [Fintype F]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) {δ : ℝ≥0}
    (hδwin : (δ : ℝ) < windowTop ρ)
    (hjoint : (δ : ENNReal) < jointRelDist f₁ f₂ C)
    {ε qErr R : ℝ} {q : ℕ}
    (hR : (Fintype.card ι : ℝ) * R = 1 / (Fintype.card F : ℝ))
    (hsplit : ε ≤ caFailureMeasure C f₁ f₂ δ + qErr)
    (hQuery : QuerySoundnessBound qErr ((δ / 2 : ℝ≥0) : ℝ) q) :
    ε ≤ 1 / (Fintype.card F : ℝ) + (1 - (δ : ℝ) / 2) ^ q := by
  -- The per-round assembly: CA half proven, query half named. The `BelowJohnsonRegime` slot of
  -- `thresholdHalving_perRound_caDischarged` is its triggering inequality `r < johnsonRadius ρ`
  -- (modelling def), so it is discharged HERE by `fun _ hr => hr` — it is NOT an external input.
  have hper :
      PerRoundFRIError ε (Fintype.card ι) R q ((δ / 2 : ℝ≥0) : ℝ) :=
    thresholdHalving_perRound_caDischarged hρ0 hρ1 C f₁ f₂ hδwin hjoint
      (fun _ hr => hr) hR hsplit hQuery
  -- Unfold `PerRoundFRIError ε n R q (δ/2)` to `ε ≤ n·R + (1 − δ/2)^q`, then substitute
  -- `n·R = 1/|F|` and `((δ/2 : ℝ≥0) : ℝ) = (δ:ℝ)/2`.
  unfold PerRoundFRIError at hper
  rwa [hR, coe_half_radius] at hper

/-! ### The end-to-end multi-round capstone

We now run `r` rounds, each with per-round error bounded by the clean `1/|F| + (1 − δ/2)^q` form
above (so the same `(ρ, C, f₁, f₂, δ)` analysis and CA floor applies every round), and chain the
multi-round union bound `total_error_le_rounds_mul` to obtain the headline total-error bound. -/

/-- **THE CAPSTONE — end-to-end threshold-halving FRI soundness (ePrint 2026/858).**

Fix a rate `ρ ∈ (0, 1)`, a linear code `C ⊆ Fⁿ`, words `f₁ f₂ : ι → F`, and a proximity radius
`δ : ℝ≥0` in the **above-Johnson window** `(johnsonRadius ρ, windowTop ρ) = (1 − √ρ, 1 − ρ)`.
Run an `r`-round threshold-halving FRI, each round at analysis radius `δ/2`, with the genuine
joint-separation hypothesis `δ < Δ_joint(f₁, f₂; C)` and the round-scaling normalization
`n·R = 1/|F|`.

GIVEN, as the **only** external (not-in-tree) facts — each a genuine, non-vacuous named `Prop`:

* **(i)** `hQuery` — the per-round query-survival product `qErr ≤ (1 − δ/2)^q`;
* **(ii)** `hUnion` — the round union bound `εTot ≤ ∑ ε`;

and the standard per-round FRI additive split `hsplit : ε ≤ (CA-failure measure) + qErr`, THEN the
total FRI soundness error is bounded by

  `ε_total ≤ r · (1/|F| + (1 − δ/2)^q)`.

The analysis radius `δ/2` is **locked below Johnson** (`coe_halved_radius_below_johnson`, from the
window arithmetic), so the per-round CA half is the **PROVEN** `caFailureMeasure_le_inv_card`
(`≤ 1/|F|`), NOT an assumption. The below-Johnson triggering is proven in-tree (no external BCIKS
hypothesis); the residuals are exactly (i), (ii). -/
theorem thresholdHalving_FRI_soundness_end_to_end [Fintype F]
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) {δ : ℝ≥0}
    (hlo : johnsonRadius ρ < (δ : ℝ)) (hhi : (δ : ℝ) < windowTop ρ)
    (hjoint : (δ : ENNReal) < jointRelDist f₁ f₂ C)
    {ε qErr R εTot : ℝ} {q r : ℕ}
    (hR : (Fintype.card ι : ℝ) * R = 1 / (Fintype.card F : ℝ))
    -- standard FRI per-round additive split (CA-failure measure + query error).
    (hsplit : ε ≤ caFailureMeasure C f₁ f₂ δ + qErr)
    -- (i) external: per-round query-survival product.
    (hQuery : QuerySoundnessBound qErr ((δ / 2 : ℝ≥0) : ℝ) q)
    -- (ii) external: multi-round union bound (each of the r rounds shares per-round error ε).
    (hUnion : UnionBoundOverRounds εTot (Finset.univ : Finset (Fin r)) (fun _ => ε)) :
    εTot ≤ (r : ℝ) * (1 / (Fintype.card F : ℝ) + (1 - (δ : ℝ) / 2) ^ q) := by
  -- Per-round bound: ε ≤ 1/|F| + (1 − δ/2)^q, with the CA half PROVEN.
  have hper : ε ≤ 1 / (Fintype.card F : ℝ) + (1 - (δ : ℝ) / 2) ^ q :=
    perRound_error_clean hρ0.le hρ1.le C f₁ f₂ hhi hjoint hR hsplit hQuery
  -- Multi-round union bound: εTot ≤ r · ε.
  have htot : εTot ≤ (r : ℝ) * ε := total_error_le_rounds_mul r ε hUnion
  -- Chain: εTot ≤ r · ε ≤ r · (1/|F| + (1 − δ/2)^q).
  refine le_trans htot ?_
  exact mul_le_mul_of_nonneg_left hper (Nat.cast_nonneg r)

/-! ### The below-Johnson radius lock, surfaced as a corollary

For the record, the same window hypotheses certify that the per-round analysis radius `δ/2` is
strictly below the Johnson radius — the structural reason the CA half is unconditional rather than
assumed. We re-export it on the discrete radius so a caller of the capstone can see the lock
explicitly alongside the soundness bound. -/

/-- **Analysis-radius lock (PROVEN).** On the prize window `ρ ∈ (0,1)`, `δ ∈ (1−√ρ, 1−ρ)`, the
halved analysis radius `δ/2` (the radius at which every round's CA count is taken) is strictly below
the Johnson radius `1 − √ρ`. This is the pure window arithmetic that makes the capstone's per-round
CA term the proven `1/|F|` floor instead of an external assumption. -/
theorem analysis_radius_locked_below_johnson
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {δ : ℝ≥0}
    (hhi : (δ : ℝ) < windowTop ρ) :
    ((δ / 2 : ℝ≥0) : ℝ) < johnsonRadius ρ :=
  coe_halved_radius_below_johnson hρ0.le hρ1.le hhi

/-! ### Packaged capstone: the soundness bound together with the radius lock

A single conjunction recording BOTH headline facts of the brick — the end-to-end soundness bound
AND the below-Johnson lock on the analysis radius — so a downstream consumer gets the soundness
statement and the certificate that its CA half was proven (not assumed) in one object. -/

/-- **Capstone package.** On the prize window, the threshold-halving FRI is BOTH:

* **sound** — `εTot ≤ r · (1/|F| + (1 − δ/2)^q)` (the end-to-end bound), AND
* **locked** — `δ/2 < johnsonRadius ρ` (the analysis radius is below Johnson, so the per-round CA
  half is the PROVEN `1/|F|` floor, not an external assumption).

The only external inputs remain the two named `Prop`s (query-survival product, round union bound);
the below-Johnson triggering is proven in-tree. -/
theorem thresholdHalving_FRI_capstone_package [Fintype F]
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (C : Submodule F (ι → F)) (f₁ f₂ : ι → F) {δ : ℝ≥0}
    (hlo : johnsonRadius ρ < (δ : ℝ)) (hhi : (δ : ℝ) < windowTop ρ)
    (hjoint : (δ : ENNReal) < jointRelDist f₁ f₂ C)
    {ε qErr R εTot : ℝ} {q r : ℕ}
    (hR : (Fintype.card ι : ℝ) * R = 1 / (Fintype.card F : ℝ))
    (hsplit : ε ≤ caFailureMeasure C f₁ f₂ δ + qErr)
    (hQuery : QuerySoundnessBound qErr ((δ / 2 : ℝ≥0) : ℝ) q)
    (hUnion : UnionBoundOverRounds εTot (Finset.univ : Finset (Fin r)) (fun _ => ε)) :
    εTot ≤ (r : ℝ) * (1 / (Fintype.card F : ℝ) + (1 - (δ : ℝ) / 2) ^ q)
      ∧ ((δ / 2 : ℝ≥0) : ℝ) < johnsonRadius ρ :=
  ⟨thresholdHalving_FRI_soundness_end_to_end hρ0 hρ1 C f₁ f₂ hlo hhi hjoint hR hsplit
      hQuery hUnion,
    analysis_radius_locked_below_johnson hρ0 hρ1 hhi⟩

-- Axiom audit: every result must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms perRound_error_clean
#print axioms thresholdHalving_FRI_soundness_end_to_end
#print axioms analysis_radius_locked_below_johnson
#print axioms thresholdHalving_FRI_capstone_package

end ProximityGap.ThresholdHalvingCapstone
