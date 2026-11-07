/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._wf7W3_HypercontractiveStepAntitone

/-!
# wf-B3: an abstract observation — a single rising step ratio falsifies `StepRatioAntitone` —
plus (unformalized) probe data suggesting the char-`p` step ratio can rise (#444)

## The target

[W3-anti] of the Proximity-Prize moment reduction is the **step-ratio antitonicity**

> `StepRatioAntitone M n`  :  `R(r+1) ≤ R(r)` for all `r ≥ 1`,  where
> `R(r) = NormStepRatio M n r = M(r+1) / ((2r+1)·n·M(r))`

(`WF7W3`). Together with the base `R(1) ≤ 1` it is the in-tree route
`gaussian_moment_bound_of_antitone_base` to the full Wick bound `M(r) ≤ (2r-1)‼·n^r`.

## The companion lanes (accurately)

* **B2 (`_wf8B2_char0_logconcave.lean`)** reduces char-`0` antitonicity to the sharp Newton
  inequality: `char0_W3anti_of_sharpNewton` is CONDITIONAL on the hypothesis
  `SharpNewtonBessel d`.  In-tree that hypothesis is discharged only at low orders (e.g.
  `CharZeroSharpNewtonR2.sharpNewton_two` for `r = 2`), not in general.  So char-`0` W3-anti is
  NOT proved in-tree in general.
* **B1 (`_wf8B1_kurtosis_cap.lean`)** proves the kurtosis cap `mu_n_kurtosis_cap` (the W3-base
  rung, under its own hypotheses); it does not break W3-base.

## Probe data (NOT formalized, and not independently reproduced)

`probe_wf8B3_antitone_adversarial.rs` / `probe_wf8B3_failure_anatomy.rs` reported a non-monotone
bump in the char-`p` normalised step ratio, e.g. at `n = 32`, `p = 1 001 153` (`β ≈ 3.99`, just
below `n⁴ = 1 048 576`): `R(4) = 0.9219 < R(5) = 0.9323`, and sub-prize bumps at `p = 4129`
(`n = 32`) and `p = 15233` (`n = 128`).  An independent exact recomputation of the non-principal
step ratio at `n = 32`, `p = 1 001 153` (audit 2026-10-28) found it monotonically DECREASING there
(`R(4) ≈ 0.886`, `R(5) ≈ 0.876`), i.e. it did NOT reproduce the claimed bump.  The char-`p`
failure of W3-anti is therefore an open empirical question, not an established obstruction.

## What this file proves (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `stepRatio_rise_breaks_antitone` — the abstract mechanism: if at some `r ≥ 1` the step ratio
  strictly rises, `R(r) < R(r+1)`, then `StepRatioAntitone` fails.  (Immediate from the definition.)
* `bumpWitness` — a hand-typed rational sequence (constant `1` off `{4,5,6}`) whose step ratios at
  `r = 4, 5` are `9219/10000 < 9323/10000` (the probe's reported values).  It is NOT a Gauss-period
  moment sequence and carries no information about any actual `μ_n` or prime.
* `antitone_FALSE_at_bump` — `¬ StepRatioAntitone bumpWitness 32` (rational `norm_num` check).
* `exists_not_stepRatioAntitone` — `∃ M n, ¬ StepRatioAntitone M n`.  This holds for any sequence
  with a rising step ratio and says nothing about char-`p` Gauss-period moments; it does NOT show
  the antitone route `WF7W3.gaussian_moment_bound_of_antitone_base` fails for the prize moments.

Issue #444, lane wf-B3.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.WF8B3

open ArkLib.ProximityGap.Frontier.WF7W3

/-! ## The general mechanism: a local log-convex rung breaks antitonicity -/

/-- **The general obstruction mechanism.** `NormStepRatio M n r = M(r+1)/((2r+1)·n·M(r))`. If at
some `r` the moment sequence is *locally log-convex* in the sharp sense
`M(r+1)·M(r+1)·((2r+3)) > M(r)·M(r+2)·((2r+1))` (after clearing the `n`-factors this is exactly
`R(r+1) > R(r)`), then the antitonicity step `R(r+1) ≤ R(r)` is violated.

(This is an abstract observation about arbitrary real sequences.) -/
theorem stepRatio_rise_breaks_antitone {M : ℕ → ℝ} {n : ℝ} {r : ℕ} (hr : 1 ≤ r)
    (hrise : NormStepRatio M n r < NormStepRatio M n (r + 1)) :
    ¬ StepRatioAntitone M n := by
  intro hanti
  exact absurd (hanti r hr) (not_le.mpr hrise)

/-! ## A hand-typed abstract witness (proxy `n = 32`) -/

/-- A hand-typed rational sequence at proxy `n = 32`, engineered so that its two load-bearing
normalised step ratios are the probe-REPORTED values `R(4) = 9219/10000` and `R(5) = 9323/10000`
(so `R(4) < R(5)`).  It is not a Gauss-period moment sequence.

We solve `R(r) = M(r+1)/((2r+1)·32·M(r))` for `M`, anchoring `M(4) = 1`:
`M(5) = R(4)·9·32·M(4) = 165942/625`, `M(6) = R(5)·11·32·M(5) = 34035699852/390625`.
All other rungs are set to `1` (the witness only probes `r = 4`, the single antitone step
`R(5) ≤ R(4)`). Pure rationals — the whole obstruction is a `norm_num` check. -/
noncomputable def bumpWitness : ℕ → ℝ
  | 4 => 1
  | 5 => 165942 / 625
  | 6 => 34035699852 / 390625
  | _ => 1   -- irrelevant rungs (the witness only probes the r = 4 antitone step)

/-- **`StepRatioAntitone` fails on the hand-typed witness.** The antitone step at `r = 4` requires
`R(5) ≤ R(4)`; the witness has `R(4) = 9219/10000 < R(5) = 9323/10000`.  Rational arithmetic only;
no statement about actual char-`p` moments. -/
theorem antitone_FALSE_at_bump : ¬ StepRatioAntitone bumpWitness 32 := by
  apply stepRatio_rise_breaks_antitone (r := 4) (by norm_num)
  -- R(4) = M(5)/((9)·32·M(4));  R(5) = M(6)/((11)·32·M(5))
  show NormStepRatio bumpWitness 32 4 < NormStepRatio bumpWitness 32 5
  unfold NormStepRatio bumpWitness
  norm_num

/-- **Abstract existence.** Some real sequence violates `StepRatioAntitone`.  This holds for any
sequence with a rising step ratio; it does not show that the char-`p` Gauss-period moments violate
W3-anti, nor that `WF7W3.gaussian_moment_bound_of_antitone_base` is inapplicable to them. -/
theorem exists_not_stepRatioAntitone :
    ∃ (M : ℕ → ℝ) (n : ℝ), ¬ StepRatioAntitone M n :=
  ⟨bumpWitness, 32, antitone_FALSE_at_bump⟩

end ArkLib.ProximityGap.Frontier.WF8B3

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.WF8B3.stepRatio_rise_breaks_antitone
#print axioms ArkLib.ProximityGap.Frontier.WF8B3.antitone_FALSE_at_bump
#print axioms ArkLib.ProximityGap.Frontier.WF8B3.exists_not_stepRatioAntitone
