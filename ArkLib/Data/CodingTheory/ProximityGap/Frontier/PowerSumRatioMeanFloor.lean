/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PowerSumRatioMonotone

/-!
# The power-sum ratio at every depth dominates the base mean (#444)

Iterate of `powerSum_ratio_monotone`.

**What this extends.** `PowerSumRatioMonotone.powerSum_ratio_monotone` proved the SINGLE-STEP rise
of the consecutive power-sum ratio `S_{t+1}/S_t ≤ S_{t+2}/S_{t+1}` (log-convexity of `t ↦ log S_t`).
This file ITERATES that single step over depth to its uniform consequence:

> **For any nonnegative finite spectrum `a` with all power sums positive, the depth-`t` consecutive
> ratio `S_{t+1}/S_t` is at least the base ratio `S_1/S_0` (the arithmetic mean of the spectrum):**
> `S_1/S_0 ≤ S_{t+1}/S_t` for every `t`.

Since `S_0 = card ι` and `S_1 = ∑_i a_i`, the base ratio `S_1/S_0` is exactly the arithmetic mean of
the spectrum. Combined with `PowerSumRatioMonotone.powerSum_ratio_le_max` (`S_{t+1}/S_t ≤ max a`),
this pins the WHOLE ratio ladder into the band `[mean a, max a]`, with the lower endpoint a fixed,
explicit, depth-independent floor (the mean) and the rungs rising monotonically from it toward
`max a`. On the prize spectrum (`a_i = ‖η_{b_i}‖²` over the `b ≠ 0` frequencies, `max a = M(n)²`),
this is the honest statement that the rising lower-bracket on `M(n)²` starts no lower than the mean
square of the Gauss periods.

## The mechanism (induction over the proven single step)

`powerSum_ratio_monotone` gives `r_t ≤ r_{t+1}` for `r_t := S_{t+1}/S_t` (when `S_t, S_{t+1} > 0`).
A finite chain of these transitivities from depth `0` up to depth `t` yields `r_0 ≤ r_t`, i.e.
`S_1/S_0 ≤ S_{t+1}/S_t`. The only side condition is positivity of the power sums along the chain,
supplied uniformly by `a ≠ 0` componentwise on a nonempty support (here packaged as a hypothesis
`∀ s, 0 < ∑ a^s`, which holds e.g. whenever some `a_i > 0`, since `a_i^s > 0` for that `i`).

## What is PROVEN here (axiom target `{propext, Classical.choice, Quot.sound}`)

* `powerSum_ratio_ge_base` — `S_1/S_0 ≤ S_{t+1}/S_t` for all `t`, the depth-uniform mean floor on
  the ratio ladder, obtained by iterating `powerSum_ratio_monotone`.

## Honesty / scope (rules 1,3,6 + ASYMPTOTIC GUARD)

Field-universal structural identity on an arbitrary nonnegative spectrum (holds for the thick group
too, by rule 3 it therefore cannot and does not prove the thinness-essential prize). It is a LOWER
bound on `max a = M(n)²` (the EASY/honest direction), tightening the in-tree lower bracket with an
explicit depth-independent floor. NOT the wall-bearing UPPER bound; no CORE closure, no char-p
transfer, no capacity / beyond-Johnson / growth-law claim; structurally orthogonal to the
cliff-at-n/2 (a lower bound). Pure iterate of a proven single-step monotonicity — no new analytic
input.

Probe `scripts/probes/probe_psratio_iterate.py`: `0 fails / 59038` random nonnegative spectra
(`S_{t+1}/S_t ≥ S_1/S_0` at every depth `t = 0..6`). (The same probe also REFUTED a naive
`min_support a ≤ S_{t+1}/S_t` envelope — `2681` fails — so the floor is the MEAN, not the support
min; this file formalizes only the verified mean floor.)

## References
- `PowerSumRatioMonotone.powerSum_ratio_monotone` (the single-step rise iterated here).
- `PowerSumRatioMonotone.powerSum_ratio_le_max` (the matching upper cap `≤ max a`).
- `_MomentLadderAntitone.ladder_antitone` (the antitone UPPER root side of the same localization).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
-/

open Finset

namespace ProximityGap.Frontier.PowerSumRatioMeanFloor

open ProximityGap.Frontier.PowerSumRatioMonotone

variable {ι : Type*}

/-- **The power-sum ratio at every depth dominates the base mean.** For a nonnegative family
`a : ι → ℝ` over a finite index with all power sums positive (`∀ s, 0 < ∑ a_i^s`), the consecutive
ratio `S_{t+1}/S_t` is bounded below by the base ratio `S_1/S_0 = (∑ a_i)/(card ι)`, the arithmetic
mean of the spectrum, uniformly in `t`. Proof: induction on `t`, transitively chaining the
single-step `powerSum_ratio_monotone`. -/
theorem powerSum_ratio_ge_base [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hpos : ∀ s, 0 < ∑ i, (a i) ^ s) (t : ℕ) :
    (∑ i, (a i) ^ (1 : ℕ)) / (∑ i, (a i) ^ (0 : ℕ))
      ≤ (∑ i, (a i) ^ (t + 1)) / (∑ i, (a i) ^ t) := by
  induction t with
  | zero => exact le_refl _
  | succ n ih =>
    refine le_trans ih ?_
    exact powerSum_ratio_monotone a ha n (hpos n) (hpos (n + 1))

end ProximityGap.Frontier.PowerSumRatioMeanFloor

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.PowerSumRatioMeanFloor.powerSum_ratio_ge_base
