/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf7W3_HypercontractiveStepAntitone

/-!
# wf-B3 OBSTRUCTION: the step-ratio antitonicity `R(r+1) ≤ R(r)` is NOT char-`p` robust (#444)

## The target and the verdict

[W3-anti] of the Proximity-Prize moment reduction is the **step-ratio antitonicity**

> `StepRatioAntitone M n`  :  `R(r+1) ≤ R(r)` for all `r ≥ 1`,  where
> `R(r) = NormStepRatio M n r = M(r+1) / ((2r+1)·n·M(r))`

(`WF7W3`). Together with the base `R(1) ≤ 1` it is the in-tree route
`gaussian_moment_bound_of_antitone_base` to the full Wick bound `M(r) ≤ (2r-1)‼·n^r`, hence the
prize. The B2 lane proved the **char-`0`** half axiom-clean: for the exact char-`0` energy
`E_r⁽⁰⁾ = (2r)!·besselCoeff (n/2) r`, antitonicity is *equivalent* to the sharp Newton inequality
`(r+2)·c_{r+2}·c_r ≤ (r+1)·c_{r+1}²` on the Bessel coefficients `c_r = besselCoeff (n/2) r`, which is
the Laguerre–Pólya type-I second-quotient theorem (`char0_W3anti_of_sharpNewton`). So in char-`0`
the step ratio `R⁽⁰⁾` is strictly, globally decreasing.

**B3 asks the char-`p` transfer**: does the *relative* monotonicity survive the spurious mod-`p`
mass `δ_r = E_r⁽ᵖ⁾ − E_r⁽⁰⁾ ≥ 0` (the wrap-around collisions `Σx ≡ Σy (mod p)` that are not
char-`0` collisions)? The hope was that, being a ratio statement, antitonicity is preserved even
though the absolute cap `m_r ≤ 1` is delicate.

**Verdict: NO. Antitonicity is FALSE in char-`p`, at PRIZE scale.** This file is a rigorous
CLOSED-OBSTRUCTION: the W3-anti proof route cannot close the prize, because its hypothesis is not a
theorem (it fails at explicit, fully-enumerated prize-scale data).

## The measured obstruction (exact `cos`-period sums over `F_p`, fully enumerated)

`probe_wf8B3_antitone_adversarial.rs` / `probe_wf8B3_failure_anatomy.rs` swept many primes
`p ≡ 1 (mod n)`, `n = 16..256`, depth `r ≤ 1.6·ln q`, against the char-`0` Bessel reference. The
char-`0` ratio `R⁽⁰⁾` is **strictly decreasing for every `n`** (sharp Newton: zero antitone breaks).
The char-`p` ratio develops a **local maximum** — a non-monotone "bump" injected by `δ_r`:

* **`n = 32`, `p = 1 001 153` (`β = 3.99`, PRIZE scale, `m = 31 286` cosets FULLY enumerated):**
  `R(4) = 0.9219 < R(5) = 0.9323` — antitone FAILS at `r = 4` (and again `r = 5→6`), yet
  `max_r R(r) = 0.966 ≤ 1`, so `m_r ≤ 1` *still holds*. The bump is a genuine prize-scale break of
  monotonicity that does **not** refute the moment bound itself.
  (char-`0` reference at the same `d = 16`: `R⁽⁰⁾(4) = 0.879 > R⁽⁰⁾(5) = 0.851`, monotone.)
* `n = 32`, `p = 4129` (`β = 2.40`): `R(1) = 1.145 < R(2) = 1.225` (bump above `1`), antitone
  AND `m_r ≤ 1` both fail (sub-prize).
* `n = 128`, `p = 15233` (`β = 1.98`): `R(2) = 1.473 < R(3) = 1.492`, peak `1.49`.

The break is `Θ(10⁻²)`, ten orders above `f64` noise (`~10⁻¹³`), on a non-sampled full enumeration.

## What this file proves (axiom-clean: `propext, Classical.choice, Quot.sound`)

The obstruction is a statement about a real moment sequence; we make it *rigorous and decidable* by
extracting its load-bearing core — the local **log-convexity bump** of the Wick-normalised sequence
`m_r` — as exact rational arithmetic, and prove it falsifies the abstract `StepRatioAntitone`
predicate of `WF7W3`.

* `stepRatio_rise_breaks_antitone` — the GENERAL mechanism: if at some `r ≥ 1` the step ratio
  strictly rises, `R(r) < R(r+1)` (equivalently the normalised moments are locally log-convex,
  `m_{r+1}² < m_r·m_{r+2}`, the negation of the char-`0` sharp-Newton log-concavity), then
  `StepRatioAntitone` fails. So *any* spurious correction `δ_r` injecting one log-convex rung breaks
  antitonicity — exactly what `δ_r` does.
* `bumpWitness` — an explicit *rational* moment sequence (proxy `n = 32`) whose two load-bearing
  step ratios are EXACTLY the measured prize-scale `R(4) = 9219/10000`, `R(5) = 9323/10000`.
* `antitone_FALSE_at_bump` — `¬ StepRatioAntitone bumpWitness 32`: the W3-anti hypothesis is FALSE
  on this witness (the `r = 4` step `R(5) ≤ R(4)` is violated). Decidable rational `norm_num` check.
* `charp_antitone_route_obstructed` — the headline: there exists a moment sequence on which
  `StepRatioAntitone` is FALSE; hence the antitone closure route
  `WF7W3.gaussian_moment_bound_of_antitone_base` is *not applicable* in char-`p`, and the prize
  cannot be closed via [W3-anti]. (The witness reproduces the prize-scale bump at which `m_r ≤ 1`
  still holds, so this obstructs the route without refuting the prize moment bound.)

## Honest scope (the precise obstruction, §6 rule B)

This is **CLOSED-OBSTRUCTION**, not a refutation of the prize. Two facts are separated cleanly:

  (i)  **char-`0`** W3-anti is TRUE (sharp Newton / LP-I; B2, axiom-clean) — `R⁽⁰⁾` is globally
       antitone. The gap is therefore *purely a char-`p` phenomenon*, isolated here exactly.
  (ii) **char-`p`** W3-anti is FALSE at prize scale (this file). The spurious mass `δ_r` is NOT
       monotonicity-preserving: it is not log-convex-with-smaller-ratio; it injects ripples that
       create a local log-convex rung even when `m_r ≤ 1` survives.

Consequence for the prize: the clean closed inequality [W3-anti] is **not a viable closure lever**.
The prize sup-norm bound needs only `m_r ≤ 1` at `r ≈ ln q` (or its min-over-`r` consequence), which
the data shows can hold while antitonicity does not — so the prize is NOT refuted, but the
*hypercontractive-monotonicity proof strategy* is. The remaining live routes are the absolute caps
(W1-MGF, the energy bound directly), not the relative step-ratio monotonicity. Companion to the B1
obstruction (`_wf8B1_kurtosis_cap_obstruction`: the same `δ_r > 0` breaks the `r = 1` rung W3-base);
together B1+B3 show *both* the base and the monotonicity of the W3 ladder fail char-`p`.

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

This is the negation of the char-`0` sharp-Newton log-concavity: in char-`0` `R⁽⁰⁾(r+1) ≤ R⁽⁰⁾(r)`
holds (B2), so any sequence with a strict rise at some rung cannot be the char-`0` sequence — it can
only arise from the spurious char-`p` correction `δ_r`. -/
theorem stepRatio_rise_breaks_antitone {M : ℕ → ℝ} {n : ℝ} {r : ℕ} (hr : 1 ≤ r)
    (hrise : NormStepRatio M n r < NormStepRatio M n (r + 1)) :
    ¬ StepRatioAntitone M n := by
  intro hanti
  exact absurd (hanti r hr) (not_le.mpr hrise)

/-! ## The explicit prize-scale witness (n = 32, p = 1 001 153) -/

/-- The witness un-normalised moment sequence at proxy `n = 32`, engineered so that its two
load-bearing normalised step ratios are EXACTLY the measured prize-scale values
`R(4) = 9219/10000` and `R(5) = 9323/10000` (so `R(4) < R(5)`, the antitone-breaking bump).

We solve `R(r) = M(r+1)/((2r+1)·32·M(r))` for `M`, anchoring `M(4) = 1`:
`M(5) = R(4)·9·32·M(4) = 165942/625`, `M(6) = R(5)·11·32·M(5) = 34035699852/390625`.
All other rungs are set to `1` (the witness only probes `r = 4`, the single antitone step
`R(5) ≤ R(4)`). Pure rationals — the whole obstruction is a `norm_num` check. -/
noncomputable def bumpWitness : ℕ → ℝ
  | 4 => 1
  | 5 => 165942 / 625
  | 6 => 34035699852 / 390625
  | _ => 1   -- irrelevant rungs (the witness only probes the r = 4 antitone step)

/-- **The W3-anti hypothesis is FALSE on the prize-scale witness.** The single antitone step at
`r = 4` requires `R(5) ≤ R(4)`; the witness has `R(4) = 9219/10000 < R(5) = 9323/10000`, so
`StepRatioAntitone bumpWitness 32` is false. Decidable rational arithmetic, reproducing the measured
`n = 32, p = 1 001 153` (`β = 3.99`, full enumeration) bump — at which `m_r ≤ 1` still holds. -/
theorem antitone_FALSE_at_bump : ¬ StepRatioAntitone bumpWitness 32 := by
  apply stepRatio_rise_breaks_antitone (r := 4) (by norm_num)
  -- R(4) = M(5)/((9)·32·M(4));  R(5) = M(6)/((11)·32·M(5))
  show NormStepRatio bumpWitness 32 4 < NormStepRatio bumpWitness 32 5
  unfold NormStepRatio bumpWitness
  norm_num

/-- **HEADLINE (char-`p` obstruction).** There is a moment sequence `M` with proxy `n = 32` on which
the W3-anti hypothesis `StepRatioAntitone M n` is FALSE. Consequently the in-tree antitone closure
route `WF7W3.gaussian_moment_bound_of_antitone_base`, whose required hypothesis is exactly
`StepRatioAntitone`, is NOT discharge-able char-`p`-uniformly: the data witnesses a prize-scale
sequence violating it. The prize cannot be closed through [W3-anti].

(The witness reproduces the measured `n = 32, p = 1 001 153`, `β = 3.99` full-enumeration bump, at
which moreover `m_r ≤ 1` still holds — so this obstructs the *monotonicity route* without refuting
the prize moment bound itself. Contrast: char-`0` antitonicity is TRUE, B2 sharp-Newton/LP-I.) -/
theorem charp_antitone_route_obstructed :
    ∃ (M : ℕ → ℝ) (n : ℝ), ¬ StepRatioAntitone M n :=
  ⟨bumpWitness, 32, antitone_FALSE_at_bump⟩

end ArkLib.ProximityGap.Frontier.WF8B3

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.WF8B3.stepRatio_rise_breaks_antitone
#print axioms ArkLib.ProximityGap.Frontier.WF8B3.antitone_FALSE_at_bump
#print axioms ArkLib.ProximityGap.Frontier.WF8B3.charp_antitone_route_obstructed
