# δ* #466 — W15 part 4: the window is two-sided — L_near = 1 refuted by two-block lines; the secant dichotomy (2026-07-10)

Lane: `ll:low-profile-fiber`. File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_W15WindowTwoReference.lean`
(axiom-clean, 9/9 audits `[propext, Classical.choice, Quot.sound]`, no `sorryAx`,
`pg-iterate` 35s). Probe: `scripts/probes/probe_466_w15_window_two_reference.py`
(deterministic, exit 0). Companions: parts 1–3
(`deltastar-466-lowprofile-{mcaevent-support-ladder-floor, safe-branch-ceiling,
nearcode-johnson-budget}-2026-07-10.md`).

## 0. The task

Decide `L_near = 1` for `LargeZeroSafeLineListBudgeted` inside the
Johnson-to-doubled-Johnson window `√ρ < α ≤ (1 + √ρ)/2` — exactly where the campaign
rate-quarter shape `(n, k, a) = (16, 4, 9)` lives, and where the part-2 probe's random
lines showed `Λ = 1`.

## 1. Verdict: REFUTED — the probe's `Λ = 1` was not worst-case

**The two-block line.** `Z = B₀ ⊔ B₁` with `|B_j| = n − a`; offset `u₀ = 0` on `B₀`,
`1` on `B₁`, `0` on the `s = 2a − n` support points; direction `u₁ = 1` exactly on the
support. Then:

* the constant codeword `0` appears at `γ = 0` (agreement `B₀ ∪ S`, exactly `a`);
* the constant codeword `1` appears at `γ = 1` (agreement `B₁ ∪ S`, exactly `a`);
* the line is zero-direction-safe: constants score `n − a < a` on `Z` (each sees only its
  own block), every other codeword scores `≤ (k−1) + (k−1) < a`;
* large-zero: `|Z| = 2(n − a) ≥ a` iff `3a ≤ 2n`.

Valid whenever `1 ≤ k`, `n + 1 ≤ 2a`, `3a ≤ 2n`, `2k − 1 ≤ a`
(`not_largeZeroSafeLineListBudgeted_one`); the campaign shape satisfies all four
(`campaign_rateQuarter_L_one_refuted`). Probe-verified at `(17,16,4,9)`: `Λ = 2`, safe,
large-zero, `mcaEvent` count `2`; the census also finds a natural `Λ = 2` line whose
second codeword appears at 7 scalars.

## 2. The positive half: the secant dichotomy

* `secant_appearing_agrees_offset` (unconditional): a codeword with `≥ a` line-agreement
  at TWO distinct scalars agrees with the offset `u₀` on `≥ 2a − n` coordinates — on the
  `≥ 2a − n` common positions the direction vanishes. No large-zero, no safety, no code
  membership needed.
* `appearing_dichotomy`: every line-appearing codeword either uses a UNIQUE scalar or is
  `u₀`-pinned at threshold `2a − n`. This is the structural handle for the window's
  remaining question: multi-appearing codewords live in the per-word (Johnson-type)
  agreement list of `u₀`; single-appearing codewords are per-scalar Johnson; what is
  missing is a bound on the number of ACTIVE scalars.

## 3. The machine-pinned boundary

`three_a_trichotomy`: every shape is in exactly one of

* `2n + k ≤ 3a` — `L = 1` PROVED (part 3, UD-plus);
* `3a ≤ 2n` — `L = 1` REFUTED (this file);
* the width-`k` gap `2n < 3a < 2n + k` — undecided (side conditions `n + 1 ≤ 2a`,
  `2k − 1 ≤ a` also needed by the refuter).

The part-3 discharge is therefore essentially TIGHT.

## 4. State of the residual and next targets

* Window bracket: `2 ≤ L_near^true`, and `≤ n²/((2a−n)² − n(k−1))` where the
  doubled-Johnson margin holds; in the deep window (margin fails, e.g. the campaign
  shape) NO finite upper bound is in-tree — this is the open content of
  `LargeZeroSafeLineListBudgeted`, now sharply posed: bound the active-scalar count.
* The two-block family cannot pass `Λ = 2` at minimal support (`M ≤ 2` blocks forced by
  `z + s ≤ n`); the singleton-block scaling does not fit at the campaign shape. Whether
  `L_near^true = 2` exactly in the window is open — a targeted probe maximizing `Λ` over
  block/support trade-offs (M blocks of size `a − s`, `M(a−s) + s ≤ n`, `z ≥ a`) is the
  natural next measurement; the analysis caps constant-base families at
  `M ≤ (n−s)/(a−s)`.
* Weld consequence: at window shapes the safe large-zero branch cannot close exactly at
  the `n − a` floor via the near-code-list route at `L = 1`; the exact safe-branch budget
  in the window inherits the factor `L_near^true ∈ [2, …]`.
