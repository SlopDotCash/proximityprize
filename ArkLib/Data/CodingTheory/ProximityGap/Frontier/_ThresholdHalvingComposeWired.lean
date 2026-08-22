/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThresholdHalvingCompose
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThresholdHalvingSoundness

/-!
# Threshold-Halving Composition, WIRED to the real per-round error — #444 (BRICK L1f)

**Target.** `_ThresholdHalvingCompose.lean` proves the multi-round union-bound collapse
`ε_total ≤ r · ε` (`total_error_le_rounds_mul`) over an **abstract** constant per-round error `ε`,
and `_ThresholdHalvingSoundness.lean` defines the **genuine** per-round FRI error predicate

  `PerRoundFRIError ε n R q halfRadius  :=  ε ≤ n·R + (1 − halfRadius)^q`.

These two bricks are currently **decoupled**: the composition's `ε` is an opaque real, never tied
to the actual threshold-halving per-round bound. This file removes that gap. It imports both and
proves a single headline that *specializes the generic composition to the real per-round bound*:

  given `PerRoundFRIError εRound n R q halfRadius` (so each round's error is at most the **closed
  form** `n·R + (1 − halfRadius)^q`) for the per-round error `εRound` used in every one of the `r`
  rounds, **and** the named multi-round union bound `UnionBoundOverRounds` over those `r` rounds,
  the total soundness error is at most

  `r · (n·R + (1 − halfRadius)^q)`.

So the composition now **consumes the real `PerRoundFRIError`**, not an abstract `ε`: the right-hand
side of the final bound is the genuine threshold-halving per-round closed form scaled by the round
count `r`.

## What is proven vs. named (honest scope)

* PROVEN (pure, `sorry`/`axiom`-free, real arithmetic + the two imported lemmas):
  - `perRoundClosedForm`            : the closed-form per-round bound `n·R + (1 − halfRadius)^q`.
  - `total_error_le_rounds_mul_perRound` : `εTot ≤ r · (n·R + (1 − halfRadius)^q)` from the **real** `PerRoundFRIError` + union bound.
  - `total_error_le_rounds_perRoundClosedForm` : the same, stated with the named `perRoundClosedForm` on the RHS (re-export).
  - `perRoundClosedForm_nonneg`     : the per-round closed form is `≥ 0` under the natural sign
        hypotheses (`0 ≤ R`, `halfRadius ≤ 1`), so the total bound is a genuine soundness error.
  - `total_error_le_rounds_mul_perRoundClosedForm_nonneg` : the total bound `r · (closed form)` is `≥ 0`, i.e. not vacuously satisfied by a negative
          right-hand side.

* NAMED (imported, NOT proven here — exactly the two carried obligations of the parent bricks):
  - `UnionBoundOverRounds εTot univ (fun _ : Fin r => εRound)` — the probabilistic multi-round
    union bound (from `_ThresholdHalvingCompose`).
  - `PerRoundFRIError εRound n R q halfRadius` — the per-round FRI accounting (from
    `_ThresholdHalvingSoundness`). This is the **genuine** per-round bound; here it is *consumed*,
    upgrading the abstract `ε` of the composition to the real closed form. It is never discharged
    here — it is supplied by the caller (e.g. the `_ThresholdHalvingPerRound` layer-cake assembly).

The single new content is the **wiring**: `PerRoundFRIError εRound … unfolds to
`εRound ≤ n·R + (1 − halfRadius)^q`, which is exactly the constant per-round bound the generic
`total_error_le_rounds_mul` consumes after `le_trans`. No probabilistic step is invented.

## Honesty / scope

This is the **LOSSY (≈ 2× query) above-Johnson route**, NOT the grand zero-loss `δ*` (the open BGK
wall). Wiring only connects the composition bookkeeping to the genuine per-round closed form; it
neither sharpens the per-round error nor escapes the Johnson barrier. Everything is
`sorry`/`native_decide`/`axiom`-free except the two explicitly named imported hypotheses
(`UnionBoundOverRounds`, `PerRoundFRIError`), which are never silently discharged.
-/

namespace ProximityGap.ThresholdHalvingComposeWired

open ProximityGap.ThresholdHalvingCompose
open ProximityGap.ThresholdHalvingSoundness

/-! ### The per-round closed form

A tiny abbreviation for the genuine threshold-halving per-round error bound's right-hand side. It is
exactly the closed form `PerRoundFRIError` bounds the per-round error by. -/

/-- The per-round FRI soundness-error **closed form** `n·R + (1 − halfRadius)^q` — the right-hand
side of `PerRoundFRIError`. This is the genuine threshold-halving per-round bound; the composition
below scales it by the round count `r`. -/
def perRoundClosedForm (n : ℕ) (R : ℝ) (q : ℕ) (halfRadius : ℝ) : ℝ :=
  (n : ℝ) * R + (1 - halfRadius) ^ q

/-- `PerRoundFRIError ε n R q halfRadius` is definitionally `ε ≤ perRoundClosedForm n R q halfRadius`.
This is the exact hinge: the genuine per-round predicate *is* a bound by the closed form. -/
theorem perRoundFRIError_iff_le_closedForm
    (ε : ℝ) (n : ℕ) (R : ℝ) (q : ℕ) (halfRadius : ℝ) :
    PerRoundFRIError ε n R q halfRadius ↔ ε ≤ perRoundClosedForm n R q halfRadius :=
  Iff.rfl

/-! ### The headline: composition WIRED to the real per-round error

The generic `total_error_le_rounds_mul εTot r ε` needs a **constant** per-round bound `ε` and the
union bound over `Fin r`. We feed it the genuine per-round closed form: from
`PerRoundFRIError εRound n R q halfRadius` we extract `εRound ≤ closed form`, and the union bound is
taken over the constant round function `fun _ : Fin r => εRound`. The result is the total error
bounded by `r · (closed form)` — the composition now consumes the **real** `PerRoundFRIError`. -/

/-- **Threshold-halving composition, wired to the real per-round error.**

Run an `r`-round FRI instance where every round uses the *same* threshold-halving per-round error
`εRound`, and suppose:

* `hRound : PerRoundFRIError εRound n R q halfRadius` — the genuine per-round bound, i.e.
  `εRound ≤ n·R + (1 − halfRadius)^q` (supplied by the per-round layer-cake assembly); and
* `hUnion : UnionBoundOverRounds εTot univ (fun _ : Fin r => εRound)` — the named multi-round union
  bound over the `r` rounds.

Then the total soundness error is bounded by the per-round **closed form** scaled by `r`:

  `εTot ≤ r · (n·R + (1 − halfRadius)^q)`.

This specializes the generic `total_error_le_rounds_mul` (whose `ε` was an abstract real) to the
**actual** `PerRoundFRIError` of the threshold-halving route: the abstract `ε` is replaced by the
genuine per-round bound's closed form, so the composition consumes the real per-round error. -/
theorem total_error_le_rounds_mul_perRound
    {εTot εRound : ℝ} (r : ℕ) {n : ℕ} {R : ℝ} {q : ℕ} {halfRadius : ℝ}
    (hRound : PerRoundFRIError εRound n R q halfRadius)
    (hUnion : UnionBoundOverRounds εTot (Finset.univ : Finset (Fin r)) (fun _ => εRound)) :
    εTot ≤ (r : ℝ) * ((n : ℝ) * R + (1 - halfRadius) ^ q) := by
  -- The generic composition: total ≤ r · εRound (constant per-round error εRound).
  have hgen : εTot ≤ (r : ℝ) * εRound := total_error_le_rounds_mul r εRound hUnion
  -- The genuine per-round bound: εRound ≤ n·R + (1 − halfRadius)^q  (this IS `PerRoundFRIError`).
  have hround : εRound ≤ (n : ℝ) * R + (1 - halfRadius) ^ q := hRound
  -- Scale the per-round bound by the (nonnegative) round count r and chain.
  calc εTot ≤ (r : ℝ) * εRound := hgen
    _ ≤ (r : ℝ) * ((n : ℝ) * R + (1 - halfRadius) ^ q) :=
        mul_le_mul_of_nonneg_left hround (Nat.cast_nonneg r)

/-- The same headline, stated with the named `perRoundClosedForm` on the right-hand side — the total
error is at most `r ·` the genuine per-round closed form. A re-export of
`total_error_le_rounds_mul_perRound` through the `perRoundClosedForm` abbreviation. -/
theorem total_error_le_rounds_perRoundClosedForm
    {εTot εRound : ℝ} (r : ℕ) {n : ℕ} {R : ℝ} {q : ℕ} {halfRadius : ℝ}
    (hRound : PerRoundFRIError εRound n R q halfRadius)
    (hUnion : UnionBoundOverRounds εTot (Finset.univ : Finset (Fin r)) (fun _ => εRound)) :
    εTot ≤ (r : ℝ) * perRoundClosedForm n R q halfRadius :=
  total_error_le_rounds_mul_perRound r hRound hUnion

/-! ### Sanity: the wired bound is a genuine (nonnegative) soundness error

The per-round closed form `n·R + (1 − halfRadius)^q` is nonnegative under the natural sign
hypotheses — `0 ≤ n·R` (rate term nonnegative) and `0 ≤ 1 − halfRadius` (the analysis radius
`halfRadius = δ/2 ≤ 1`, so the survival base is in `[0,1]`). Hence `r · (closed form) ≥ 0` and the
headline bound is not vacuously satisfied by a negative RHS. -/

/-- The per-round closed form is nonnegative when the rate term is nonnegative (`0 ≤ R`, with `n ≥ 0`
automatic) and the survival base is nonnegative (`halfRadius ≤ 1`). -/
theorem perRoundClosedForm_nonneg
    {n : ℕ} {R : ℝ} {q : ℕ} {halfRadius : ℝ} (hR : 0 ≤ R) (hhalf : halfRadius ≤ 1) :
    0 ≤ perRoundClosedForm n R q halfRadius := by
  unfold perRoundClosedForm
  have h1 : (0 : ℝ) ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg n) hR
  have h2 : (0 : ℝ) ≤ (1 - halfRadius) ^ q := pow_nonneg (by linarith) q
  linarith

/-- The wired total bound `r · (closed form)` is nonnegative under the same natural sign hypotheses,
so the headline `total_error_le_rounds_mul_perRound` produces a genuine soundness error and is not
satisfied vacuously by a negative right-hand side. -/
theorem total_error_le_rounds_mul_perRoundClosedForm_nonneg
    (r : ℕ) {n : ℕ} {R : ℝ} {q : ℕ} {halfRadius : ℝ} (hR : 0 ≤ R) (hhalf : halfRadius ≤ 1) :
    0 ≤ (r : ℝ) * perRoundClosedForm n R q halfRadius :=
  mul_nonneg (Nat.cast_nonneg r) (perRoundClosedForm_nonneg hR hhalf)

-- Axiom audit: every result must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms perRoundFRIError_iff_le_closedForm
#print axioms total_error_le_rounds_mul_perRound
#print axioms total_error_le_rounds_perRoundClosedForm
#print axioms perRoundClosedForm_nonneg
#print axioms total_error_le_rounds_mul_perRoundClosedForm_nonneg

end ProximityGap.ThresholdHalvingComposeWired
