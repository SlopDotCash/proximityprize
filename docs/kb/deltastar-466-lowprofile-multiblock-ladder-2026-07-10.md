# δ* #466 — W15 part 5: the multi-block ladder — L_near = 2 is not universal; campaign shape capped at 2 (2026-07-10)

Lane: `ll:low-profile-fiber` (final rung before consolidation). File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_W15MultiBlockRefuter.lean`
(axiom-clean, 7/7 audits `[propext, Classical.choice, Quot.sound]`, no `sorryAx`,
`pg-iterate` 41s). Probe: `scripts/probes/probe_466_w15_active_scalar_ceiling.py`
(deterministic, exit 0). Companions: parts 1–4 (kb notes
`deltastar-466-lowprofile-{mcaevent-support-ladder-floor, safe-branch-ceiling,
nearcode-johnson-budget, window-two-reference}-2026-07-10.md`).

## 0. The task

After part 4 refuted `L_near = 1` at `3a ≤ 2n`, decide whether `L_near^{true} = 2`.

## 1. Probe verdict: shape-dependent

* `(11,10,2,6)`: the **three-constant-block** line (blocks of size 2 with offset
  constants 0/1/2, z = 6, support 4) is safe + large-zero with `Λ = 3`; hill-climbing
  found no more. So `L = 2` is FALSE there.
* `(17,16,4,9)` (campaign): constant blocks are capped at `M = 2` by the safety gate
  `M(k−1) < a` (`9 ≥ 9`); the structured non-constant three-piece search found **0
  feasible triples in 4000 samples** (a third codeword needs ≥ 7 coordinated pairwise
  Z-overlap points among degree-<4 codewords); hill-climbs at `z ∈ {9, 14}` topped out at
  `Λ = 2`. Empirical ceiling `2` — measurement, not proof.

## 2. What is proved

1. `not_largeZeroSafeLineListBudgeted_two` — **the three-block refuter**: for any block
   size `b` with `a ≤ 3b`, `a + 2b ≤ n`, `b + 1 ≤ a`, `3(k−1) + 1 ≤ a`, `1 ≤ k`, and any
   `μ ∉ {0, 1}`: `LargeZeroSafeLineListBudgeted dom k a 2` is FALSE. The constants
   `0, 1, μ` all appear (each scores its block `b` plus the whole support `n − 3b`,
   total `n − 2b ≥ a`); the line is safe (constants score `b ≤ a − 1` on `Z`, generic
   codewords `≤ 3(k−1) < a`).
2. `elevenShape_L_two_refuted` — `(n, k, a) = (10, 2, 6)`, `b = 2`, over any field with
   `≥ 3` elements: `L_near^{true} ≥ 3`.
3. `campaign_constant_cap` — the campaign shape fails the `M = 3` gate
   (`3(k−1) + 1 = 10 > 9 = a`): the constant ladder cannot pass `M = 2` there.

## 3. The corrected lower ladder

`M` constant blocks of size `b` refute `L = M − 1` whenever `Mb ≥ a`, `n − (M−1)b ≥ a`,
`b ≤ a − 1`, `M(k−1) < a`, `M ≤ q`:

    L_near^{true} ≥ M_max(shape),

with `M_max ≥ 2` throughout `3a ≤ 2n` (part 4), `M_max = 3` at `(10,2,6)`-like shapes
(this file), and `M_max = 2` (for constants) at the campaign shape. The `M = 3` rung is
formalized; general `M` is a mechanical indexed-family extension, left un-landed until a
consumer needs it.

## 4. W15 lane summary after parts 1–5 (consolidation snapshot)

* **Part 1** (`_W15LargeZeroMcaEventFloor`): safe-branch `mcaEvent` floor `B ≥ n − a`
  (support ladder); pencil-scale budgets refuted.
* **Part 2** (`_W15SafeBranchLinearCeiling`): unconditional ceiling `count ≤ Λ·|supp|`;
  residual `LargeZeroSafeLineListBudgeted`; upgraded weld consumer; probe: sub-Johnson
  q-saturation, `Λ = 1` at the campaign shape on random lines.
* **Part 3** (`_W15NearCodeJohnsonBudget`): offset collapse discharges the residual —
  explicit `L = n²/((2a−n)² − n(k−1))` above the doubled-Johnson margin; `L = 1` at
  `2n + k ≤ 3a`; safe branch CLOSED there (weld corollary); campaign shape not covered.
* **Part 4** (`_W15WindowTwoReference`): `L = 1` REFUTED at `3a ≤ 2n` (two-block);
  secant dichotomy; trichotomy — the UD-plus discharge is tight up to a width-`k` gap.
* **Part 5** (this file): `L = 2` refuted at `(10,2,6)`-shapes (three-block); ladder is
  shape-dependent; campaign shape constant-capped at 2 with empirical ceiling 2.

**Open residuals of the lane** (honest, machine-pinned): (a) `Λ ≤ 2` at shapes with
`3(k−1) ≥ a` in the deep window (or a non-constant refuter) — the secant dichotomy is
the handle; (b) the width-`k` trichotomy gap `2n < 3a < 2n + k`; (c) the unsafe
large-zero branch `hunsafe`; (d) the far-line list budget `hfarL` (terminal).
