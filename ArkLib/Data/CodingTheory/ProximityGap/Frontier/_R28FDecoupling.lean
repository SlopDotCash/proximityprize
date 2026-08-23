/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R27FMixedMoment

/-!
# R28F (#466 round 28F, DECOUPLE lane): the cross-block mixed moment FACTORIZES

## The target

`MixedMainResHalfCS S A B (1/2)` (defined in R27F): the cross-block 4-character moment
`∑_{s₀} A²B² ≤ (1/2)·√(∑A⁴)·√(∑B⁴)`, `A = M'.re` on the Y-block characters,
`B = Res.re` on the complement block.  This is THE object that fires the r=2 subfamily
rung (`R27G.mixed_rung_fires_at_half`) — the open cross-block decoupling statement.

## The probe (`scripts/probes/probe_r28f_decouple.py`, exact cells `p ∈ {97,193,257,1153,40961}`)

Step-1 measurement of the Cauchy–Schwarz ratio `κ = (∑A²B²)/(√(∑A⁴)·√(∑B⁴))` and the
"independent value" `V = (∑A²)(∑B²)/q`:

| cell (offD rung domain) | κ = Q1 | corr `=∑A²B²/V` | fA | fB |
|-------------------------|--------|-----------------|------|------|
| p=97,   d=8, m'=2       | 0.4163 | 0.855 | 0.769 | 0.633 |
| p=193,  d=8, m'=2       | 0.4804 | 1.177 | 0.723 | 0.565 |
| p=1153, d=8, m'=2       | 0.4938 | 1.196 | 0.641 | 0.645 |
| p=40961,d=4, m'=4       | 0.3441 | 0.989 | 0.583 | 0.597 |

where `fA = (∑A²)/(√q·√(∑A⁴))`, `fB = (∑B²)/(√q·√(∑B⁴))` are the per-block flatness
(2nd-vs-4th-moment) factors.

## Two findings

**(1) Mechanism (a) is REFUTED.**  There is NO elementary exact/parity `κ = 1/2` identity:
`κ` wanders `0.34–0.55` across cells, and on the FULL domain (all `s₀`) it EXCEEDS `1/2`
(`κ = 0.549` at `p=257, d=4`).  The `κ ≤ 1/2` bound is genuinely arithmetic and holds only
on the rung domain (`s₀ ∉ G∪{0}`), where measured `κ ≤ 0.4938 < 1/2` (thin slack).

**(2) The EXACT FACTORIZATION (mechanism (b), structural reduction).**  At every cell,
machine-checked to `1e-9`:
```
      κ  =  corr · fA · fB          (Ccov · flatnessA · flatnessB)
```
i.e. the cross-block object splits as a **covariance decoupling** factor
`corr = (∑A²B²)·q/((∑A²)(∑B²))` times **two single-block flatness** factors.  This isolates
the only genuinely-cross piece (the covariance identity `∑A²B² ≈ (∑A²)(∑B²)/q`, `corr → 1`
as `q → ∞`: measured `0.99–1.03` at `p=40961`) from per-block flatness — each of which is a
2nd-vs-4th moment ratio on ONE character block (an r17/r26-type single-block object).

## What is PROVEN here (axiom-clean)

The reduction is an ELEMENTARY Cauchy–Schwarz/positivity composition:

* `CovarianceDecoupling S A B Ccov Q` : `∑A²B² ≤ Ccov·(∑A²)(∑B²)/Q`  (the cross piece)
* `BlockFlatness S A c rt`            : `∑A² ≤ c·rt·√(∑A⁴)`  (per-block, `rt = √Q`)
* `mixedMainResHalfCS_of_decoupling`  : covariance + flatness(A) + flatness(B) at `Q = rt²`
  ⟹ `MixedMainResHalfCS S A B (Ccov·cA·cB)`.
* `mixedMainResHalfCS_mono` : the `κ`-bound weakens in `κ`, so `κ₀ = Ccov·cA·cB ≤ 1/2`
  upgrades to `MixedMainResHalfCS S A B (1/2)` — the exact input `R27G` consumes.

## What remains OPEN (named, probe-calibrated — NO closure claimed)

The three inputs are the open content, now SEPARATED by role:
* `CovarianceDecoupling … Ccov` with `Ccov ≤ ~1.2` (→1): the genuine cross-block covariance —
  a 4-character `∑_{s₀} T_a conj T_b T_c conj T_d` object needing a Weil-family input.
* `BlockFlatness A cA`, `BlockFlatness B cB` with `cA·cB·Ccov ≤ 1/2` (measured product
  `0.34–0.49`): each a SINGLE-block 2nd-vs-4th moment bound (r17/r26 territory).

Axiom-clean target (`propext, Classical.choice, Quot.sound`).  Issue #466, round 28F.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.Frontier.R28FDecoupling

open ArkLib.ProximityGap.Frontier.R27FMixedMoment

variable {ι : Type*}

/-! ## 1. The three named inputs (probe-calibrated, OPEN) -/

/-- **Covariance decoupling** (the genuinely cross-block piece): the mixed 2nd moment is
controlled by the product of the two per-block energies over `Q` (`= q`).  Probe: the
constant `Ccov = (∑A²B²)·q/((∑A²)(∑B²))` is `0.85–1.20` and `→ 1` as `q → ∞`. -/
def CovarianceDecoupling (S : Finset ι) (A B : ι → ℝ) (Ccov Q : ℝ) : Prop :=
  ∑ s ∈ S, (A s) ^ 2 * (B s) ^ 2 ≤ Ccov * ((∑ s ∈ S, (A s) ^ 2) * (∑ s ∈ S, (B s) ^ 2) / Q)

/-- **Per-block flatness** (a single-block 2nd-vs-4th-moment ratio, `rt = √Q`): the 2nd
moment is at most `c·√q` times the root-4th-moment.  Probe: `fA, fB ∈ [0.57, 0.77]`,
tending to `≈ 0.58` as `q → ∞`.  This is an r17/r26-type single-character-block object. -/
def BlockFlatness (S : Finset ι) (A : ι → ℝ) (c rt : ℝ) : Prop :=
  ∑ s ∈ S, (A s) ^ 2 ≤ c * (rt * Real.sqrt (∑ s ∈ S, (A s) ^ 4))

/-! ## 2. The elementary reduction -/

/-- **The exact factorization reduction.**  From the covariance-decoupling input (constant
`Ccov`, over `Q = rt²`) and the two per-block flatness inputs (constants `cA`, `cB`, scale
`rt = √Q`), the cross-block Cauchy–Schwarz ratio is `≤ Ccov·cA·cB`.  This is the machine
form of the probe identity `κ = corr·fA·fB` — the DECOUPLING reduces to a covariance
identity times two single-block flatness bounds. -/
theorem mixedMainResHalfCS_of_decoupling (S : Finset ι) (A B : ι → ℝ)
    {Ccov cA cB rt : ℝ}
    (hCcov : 0 ≤ Ccov) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) (hrt : 0 ≤ rt)
    (hcov : CovarianceDecoupling S A B Ccov (rt ^ 2))
    (hfA : BlockFlatness S A cA rt) (hfB : BlockFlatness S B cB rt)
    (hrtpos : 0 < rt) :
    MixedMainResHalfCS S A B (Ccov * cA * cB) := by
  unfold MixedMainResHalfCS
  unfold CovarianceDecoupling at hcov
  unfold BlockFlatness at hfA hfB
  set SA2 := ∑ s ∈ S, (A s) ^ 2 with hSA2
  set SB2 := ∑ s ∈ S, (B s) ^ 2 with hSB2
  set sA := Real.sqrt (∑ s ∈ S, (A s) ^ 4) with hsA
  set sB := Real.sqrt (∑ s ∈ S, (B s) ^ 4) with hsB
  have hSA2nn : 0 ≤ SA2 := Finset.sum_nonneg fun s _ => by positivity
  have hSB2nn : 0 ≤ SB2 := Finset.sum_nonneg fun s _ => by positivity
  have hsAnn : 0 ≤ sA := Real.sqrt_nonneg _
  have hsBnn : 0 ≤ sB := Real.sqrt_nonneg _
  -- product of the two flatness bounds
  have hprod : SA2 * SB2 ≤ (cA * (rt * sA)) * (cB * (rt * sB)) :=
    mul_le_mul hfA hfB hSB2nn (by positivity)
  -- (cA rt sA)(cB rt sB) = cA cB rt² (sA sB)
  have hrew : (cA * (rt * sA)) * (cB * (rt * sB)) = cA * cB * rt ^ 2 * (sA * sB) := by ring
  rw [hrew] at hprod
  -- divide the covariance bound: (SA2 SB2)/rt² ≤ cA cB (sA sB)
  have hrt2 : 0 < rt ^ 2 := by positivity
  have hdiv : SA2 * SB2 / rt ^ 2 ≤ cA * cB * (sA * sB) := by
    rw [div_le_iff₀ hrt2]
    calc SA2 * SB2 ≤ cA * cB * rt ^ 2 * (sA * sB) := hprod
      _ = cA * cB * (sA * sB) * rt ^ 2 := by ring
  -- feed into covariance, multiply by Ccov ≥ 0
  calc ∑ s ∈ S, (A s) ^ 2 * (B s) ^ 2
      ≤ Ccov * (SA2 * SB2 / rt ^ 2) := hcov
    _ ≤ Ccov * (cA * cB * (sA * sB)) := by
        exact mul_le_mul_of_nonneg_left hdiv hCcov
    _ = Ccov * cA * cB * (sA * sB) := by ring

/-- **Weakening in `κ`**: the `MixedMainResHalfCS` bound gets easier as `κ` grows, so a
proof at a smaller `κ₀` upgrades to any `κ ≥ κ₀` (given nonneg root-moments).  Used to lift
the measured `κ₀ = Ccov·cA·cB ≈ 0.34–0.49` to the `κ = 1/2` input `R27G` consumes. -/
theorem mixedMainResHalfCS_mono (S : Finset ι) (A B : ι → ℝ) {κ₀ κ : ℝ}
    (hκ : κ₀ ≤ κ) (h : MixedMainResHalfCS S A B κ₀) :
    MixedMainResHalfCS S A B κ := by
  unfold MixedMainResHalfCS at h ⊢
  refine h.trans ?_
  have hcs : 0 ≤ Real.sqrt (∑ s ∈ S, (A s) ^ 4) * Real.sqrt (∑ s ∈ S, (B s) ^ 4) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right hκ hcs

/-- **End-to-end DECOUPLE step**: covariance + two block-flatness inputs whose composite
constant `Ccov·cA·cB ≤ 1/2` deliver exactly `MixedMainResHalfCS S A B (1/2)` — the single
open object that fires the r=2 subfamily rung (`R27G.mixed_rung_fires_at_half`). -/
theorem mixedMainResHalfCS_half_of_decoupling (S : Finset ι) (A B : ι → ℝ)
    {Ccov cA cB rt : ℝ}
    (hCcov : 0 ≤ Ccov) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) (hrt : 0 ≤ rt) (hrtpos : 0 < rt)
    (hcov : CovarianceDecoupling S A B Ccov (rt ^ 2))
    (hfA : BlockFlatness S A cA rt) (hfB : BlockFlatness S B cB rt)
    (hfit : Ccov * cA * cB ≤ 1 / 2) :
    MixedMainResHalfCS S A B (1 / 2) :=
  mixedMainResHalfCS_mono S A B hfit
    (mixedMainResHalfCS_of_decoupling S A B hCcov hcA hcB hrt hcov hfA hfB hrtpos)

end ArkLib.ProximityGap.Frontier.R28FDecoupling

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R28FDecoupling.mixedMainResHalfCS_of_decoupling
#print axioms ArkLib.ProximityGap.Frontier.R28FDecoupling.mixedMainResHalfCS_mono
#print axioms ArkLib.ProximityGap.Frontier.R28FDecoupling.mixedMainResHalfCS_half_of_decoupling
