/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AnomalyLocalization

/-!
# Door-(iv) lever refutation: the moment-to-max envelope multiplier is ANTITONE in moment depth,
so the fractional-moment / Harper "better-than-√" regime cannot improve the worst-case max (#444)

## Probe-grounded motivation (rule-2 + rule-5: probe before formalize; refuted lever is a result)

The one lead with a structural reason to escape the phase-blind integer-moment floor is the
multiplicative-chaos / Harper "better-than-√-cancellation" phenomenon, which lives at LOW
(fractional `q < 1`) moments.  Shaw's probe `scripts/probes/probe_fractional_moment_avg_vs_max.py`
(#444, 2026-06-21) settled it: the max-from-moment bound `(N · A_q)^{1/(2q)}`,
`A_q = E_{b≠0}|η_b|^{2q}`, is MONOTONE DECREASING in `q`.  So fractional `q < 1` give
CATASTROPHICALLY WORSE max-bounds (`q = 0.25` overshoots by `~10¹⁰`), and the bound is tightest at
high `q` (saddle `q ~ log p` = integer-moment-at-depth-log-p = the wall).  Harper's better-than-√ is
a LOW-moment / AVERAGE phenomenon that controls the TYPICAL period; the prize object `M` is the
WORST-CASE MAX, seen only by HIGH moments.  The most-promising-looking lever REDUCES.

`_AnomalyLocalization` already kernels the squeeze `max ≤ (∑ λ^r)^{1/r} ≤ (card s)^{1/r}·max`
(`moment_root_ge_max`, `moment_root_le_card_root_mul_max`), with the upper multiplier `(card s)^{1/r}
→ 1` as `r → ∞`.  The exact arithmetic content the probe demands — the DIRECTION across moment
depths — is the **antitonicity of the envelope multiplier `(card s)^{1/r}` in `r`**: a SMALLER moment
depth gives a LARGER (worse) envelope.  This file adds that monotonicity and the immediate corollary
that the integer-moment max-envelope `(card s)^{1/r}·max` cannot be improved by dropping to a smaller
moment depth.

## The load-bearing facts (this file, axiom-clean)

* **Envelope multiplier antitone in depth.**  For `1 ≤ card s` (a nonempty index set) and
  `1 ≤ r₁ ≤ r₂`, the multipliers satisfy `(card s)^{1/r₂} ≤ (card s)^{1/r₁}`.  Equivalently: the
  deeper the moment, the tighter the `card`-overshoot, monotonically.
* **No max-gain from a smaller moment.**  Hence for nonnegative `λ` bounded by `M` on `s`, the
  HIGH-moment max-envelope `(card s)^{1/r₂}·M` is `≤` the LOW-moment one `(card s)^{1/r₁}·M`: dropping
  to a smaller (more "fractional", Harper-regime) moment depth strictly cannot tighten the max bound.

This is a **refuted-lever constraint lemma** (door-(iv) Lane 3 / the no-fifth-door tetrachotomy: it
removes the fractional-moment escape from door-(i) = moment/BGK), NOT a CORE/cancellation/completion/
moment-saving/capacity claim: it bounds nothing about `M(n)` itself.  It kernels the DIRECTION in
Shaw's "average-vs-max" probe verdict — the formal reason Harper's better-than-√ average lever does
not transfer to the worst-case max.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVFractionalMomentNoMaxGain

open scoped Real

variable {ι : Type*}

/-- **Envelope multiplier antitone in moment depth.**  For a base `c ≥ 1` (the index-set
cardinality `card s`) and moment depths `1 ≤ r₁ ≤ r₂`, the `card`-overshoot multipliers obey
`c ^ (1/r₂) ≤ c ^ (1/r₁)`: a DEEPER moment gives a TIGHTER (smaller) overshoot.  This is the exact
direction of Shaw's probe `(N·A_q)^{1/(2q)}` decreasing in `q`. -/
theorem envelope_multiplier_antitone {c : ℝ} (hc : 1 ≤ c)
    {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₁₂ : r₁ ≤ r₂) :
    c ^ ((1 : ℝ) / r₂) ≤ c ^ ((1 : ℝ) / r₁) := by
  have hr₁pos : (0 : ℝ) < r₁ := by exact_mod_cast hr₁
  have hr₂pos : (0 : ℝ) < r₂ := by
    have : 1 ≤ r₂ := le_trans hr₁ hr₁₂
    exact_mod_cast this
  have hexp : (1 : ℝ) / r₂ ≤ (1 : ℝ) / r₁ := by
    apply one_div_le_one_div_of_le hr₁pos
    exact_mod_cast hr₁₂
  exact Real.rpow_le_rpow_of_exponent_le hc hexp

/-- **No max-gain from a smaller moment (the Harper-no-transfer corollary).**  For a nonempty index
set `s` (so `1 ≤ card s`), nonnegative `λ` bounded by `M ≥ 0`, and moment depths `1 ≤ r₁ ≤ r₂`, the
HIGH-moment max-envelope is at most the LOW-moment one:

    `(card s)^{1/r₂} · M ≤ (card s)^{1/r₁} · M`.

Combined with `_AnomalyLocalization.moment_root_ge_max` (the max is a floor for every moment root),
dropping to a smaller / fractional moment depth (Harper's `q < 1` regime) can only LOOSEN the
max-envelope — the average-vs-max obstruction in kerneled form. -/
theorem no_maxGain_from_smaller_moment (s : Finset ι) (hs : s.Nonempty)
    {M : ℝ} (hM : 0 ≤ M) {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₁₂ : r₁ ≤ r₂) :
    (s.card : ℝ) ^ ((1 : ℝ) / r₂) * M ≤ (s.card : ℝ) ^ ((1 : ℝ) / r₁) * M := by
  have hcard : 1 ≤ (s.card : ℝ) := by
    have : 1 ≤ s.card := Finset.Nonempty.card_pos hs
    exact_mod_cast this
  have hmul := envelope_multiplier_antitone hcard hr₁ hr₁₂
  exact mul_le_mul_of_nonneg_right hmul hM

end ArkLib.ProximityGap.Frontier.DoorIVFractionalMomentNoMaxGain

#print axioms ArkLib.ProximityGap.Frontier.DoorIVFractionalMomentNoMaxGain.envelope_multiplier_antitone
#print axioms ArkLib.ProximityGap.Frontier.DoorIVFractionalMomentNoMaxGain.no_maxGain_from_smaller_moment
