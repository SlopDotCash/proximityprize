# SYZ7: the production rate-1/2 decisive-strip map — ceiling/floor mechanisms and an empirical scan of (Johnson, 1/3) (2026-07-10)

Status: study/mapping round (docs + probe only; no new Lean landed). Consolidates the
SYZ1–SYZ6 arc into a single picture of what pins `mcaDeltaStar` at exact rate `1/2`, where the
remaining gap lives, and which theorems close it. All bracket numbers are the machine-checked
in-tree values; every reachability claim beyond the landed theorems is labelled CONJECTURE.

## 1. The current unconditional bracket (first certified prize field `P = 2^30·(2^128+192)+1`)

```
178956971/2^30 ≈ 0.16667   ≤   δ*(rate 1/2)   ≤   358612991/2^30 ≈ 0.33399
   (floor: ladder reach)                            (ceiling: SYZ6 finer grading)
```

Reference marks inside/around the gap:
- Johnson radius `1 − √ρ = 1 − √(1/2) ≈ 0.29289`.
- Degenerate-channel infimum `(1−ρ)/(2−ρ) = 1/3 ≈ 0.33333` at `ρ = 1/2`.

So the open region splits at Johnson into two conceptually different sub-strips:
- **FLOOR sub-strip `[0.16667, 0.29289]`** — pure conditional-floor territory (below Johnson, so
  every radius here is *expected good*; the obstruction is only that the unconditional floor
  machinery reaches `(1−ρ)/3 ≈ 0.1667`, not Johnson).
- **CEILING/decisive strip `[0.29289, 1/3]`** — above Johnson; whether these radii are good or bad
  is genuinely open. The landed ceiling stops at `1/3⁺` (`358612991/2^30`), leaving the whole
  `[Johnson, 1/3]` band undecided from both sides.

In-tree source of each endpoint:
- Floor `178956971/2^30 = ⌊(2^29)/3⌋+1)/2^30`: `PrizeShapeRateHalfBracket.firstPrime_rateHalf_ladder_floor`,
  via `ProductionRegimeBracket.production_good_ladder_reach` (file
  `ArkLib/Data/CodingTheory/ProximityGap/ProductionRegimeBracket.lean`).
- Ceiling `358612991/2^30`: `Frontier/_SYZ6FinerGradingCeiling.lean`
  (`firstPrime_rateHalf_mcaDeltaStar_le_exact`), sharpening SYZ4 `369098751/2^30 = 11/32 − 2^-30`.

## 2. Why `1/3` is a hard wall for the ceiling side (the channel-limit theorem shape)

Every landed rate-1/2 ceiling (SYZ4, SYZ6) is built from the **degenerate-subset channel**
(SYZ1 probe → SYZ2 pencil → SYZ3 witness): a `t`-subset `S` on which both `u₀|S` and `u₁|S` are
codeword restrictions donates, for every off-`S` point `x`, one `mcaEvent`-bad scalar
`γₓ = −d₀(x)/d₁(x)` (`dᵢ = uᵢ − vᵢ`). One subset ⇒ up to `n − t` bad scalars.

The **rank budget** caps the yield. Each degenerate subset imposes `2(t−k)` parity constraints on
the `2(n−k)`-dimensional syndrome-pair space (`G87McaEventSyndromeBridge`: any stack with ≥ 64 bad
scalars forces a syzygy). So the number of stackable subsets is `D ≤ (n−k)/(t−k)`, and the total
certified bad-scalar count is at most

```
D · (n − t)  ≤  (n−k)(n−t)/(t−k).
```

Beating the production budget (`ε*·q ≈ n`) requires `D·(n−t) > n`, which with `t = (1−δ)n`,
`k = ρn` rearranges to

```
δ > (1−ρ)/(2−ρ)   [= 1/3 at ρ = 1/2].
```

**Theorem-shape (not yet a Lean theorem):** any `mcaEvent`-over-budget stack certified through the
degenerate/syzygy channel has radius `δ > (1−ρ)/(2−ρ)`. Equivalently, the channel *provably
starves* on `[0, 1/3]` — it can approach `1/3` from above (SYZ4/SYZ6) but never cross it. The
`[Johnson, 1/3]` decisive strip lies entirely below this infimum; **no degenerate-channel
construction can certify any strip radius bad.** Sharpening the ceiling into the strip therefore
requires a genuinely different (non-degenerate-subset) construction, or a matching good-side proof.

## 3. Ceiling-side loophole audit (SYZ7 question 1)

- **(a) mixed thresholds `t_j` / smaller-`t_j` piggybacking.** The `mcaEvent` witness threshold is
  fixed by the radius: every witness set must have `|S ∪ {x}| ≥ ⌈(1−δ)n⌉`. A subset with smaller
  `t_j` still has to pad its agreement set back up to the radius threshold, so it does not escape
  the rank cost of the effective threshold. SYZ5 proved the rate-1/4 analogue's integer-`D` floor
  is `1/2 > 43/96` for exactly this reason (`_SYZ5RateQuarterChannelCeiling.lean`,
  `total_complement_lower_bound`). The empirical MIX family (§4) confirms mixed sizes never beat
  budget in the strip. **No loophole.**
- **(b) near-degenerate subsets (`u|S` within distance 1 of the code).** Empirically the strongest
  refinement found: planting degeneracy on size-`(t−1)` subsets and certifying at threshold `t`
  (the "NEAR" family) yields slightly MORE bad scalars than the exact channel (it lowers the
  effective `m = t−k`, raising `D`), but it still obeys the same rank budget and starves below
  `1/3` (§4). This is a genuine sharper variant of the channel, not a barrier crossing.
  **No loophole at the probed cells** (CONJECTURE: none exists).
- **(c) unions of different stacks.** `mcaEvent`/`epsMCA` is a per-stack supremum
  (`Errors.lean:231`, `⨆ u : WordStack …`); combining different stacks does not add their bad
  counts. **No loophole.** (Confirmed by definition, not just probe.)
- **(d) curve / higher-length generator events.** The prize `mcaDeltaStar` is defined off the
  **pair** event `epsMCA` (`Fin 2`, `Errors.lean`). The `ℓ`-ary curve event `epsMCACurve`
  (`MCACurveEvent.lean`) is a separate extension for WHIR's power generator and does NOT feed the
  prize threshold. CONJECTURE (not needed for the prize): for `L`-row curves a single degenerate
  subset would solve a degree-`(L−1)` equation per off-`S` point, donating up to `(L−1)(n−t)` bad
  scalars — i.e. the curve channel would be *stronger* (bigger ceiling), so curve events do not
  weaken the pair-event picture and are irrelevant to the pair-event `δ*`.
- **(e) empirical scan.** See §4.

## 4. Empirical strip scan (`scripts/probes/probe_syz7_strip_scan.py`)

Cells `n=32,k=16` (`p≈2^30`) and `n=64,k=32` (`p≈2^60`), large-field regime (generic stacks
clean). Budget analogue `= n`. Radius `δ = (n−t)/n`. Families: exact channel (A), near-degenerate
`t−1` (NEAR), mixed-threshold (MIX), random low-rank control (RAND). Every certified scalar is
FULLY verified against the literal `mcaEvent` (agreement set + ¬pairJoint, two interpolation
paths) via the SYZ1 harness. Certified **max** bad-count vs radius:

```
n=64, k=32, budget=64:
  t   delta    zone       chanBound   maxBad  verdict
  39  0.3906   above-1/3      75       104    KILLED     <- calibration: harness DOES
  40  0.3750   above-1/3      72       100    KILLED         certify over-budget when
  41  0.3594   above-1/3      46        72    KILLED         a construction exists
  42  0.3438   above-1/3      44        69    KILLED
  43  0.3281   STRIP          21        44    survives   <- 44 < 64
  44  0.3125   STRIP          20        42    survives
  45  0.2969   STRIP          19        40    survives
  46  0.2812   below-J        18        38    survives
  ...
n=32 strip (t=22, δ=0.3125): maxBad 22 < budget 32 (survives).
```

**Verdict:** NO radius in the strip `(Johnson, 1/3)` is killed by any scanned family; the harness
is validated by the calibration (every radius ABOVE `1/3` IS killed, i.e. it certifies
over-budget stacks whenever they exist). The near-degenerate variant is the strongest but still
starves below `1/3`, consistent with the §2 rank-budget wall. This is **search evidence, not a
proof** that the strip is unreachable (CONJECTURE: no construction certifies a strip radius bad,
i.e. the ceiling cannot be pushed below `1/3`).

**IMPORTANT harness caveat (fixed here):** the imported SYZ1 harness's `degenerate_rows`/
`grs_check_rows` are hardcoded to `t−k = 2` (they emit only 2 parity rows). At rate-1/2 strip
thresholds `m = t−k ≈ 5–6` this silently plants NON-degenerate stacks (first run certified 0
everywhere, including the calibration band — a red flag). `probe_syz7_strip_scan.py` supplies a
general `degenerate_rows_general` (Lagrange-interp parity rows, `2(t−k)` per subset) that fixes
this; the calibration band now behaves correctly. Any future reuse of the SYZ1 harness at `m > 2`
must use the general row builder.

## 5. Floor-side mechanism inventory (SYZ7 question 2)

| Radius reached | Theorem | Mechanism | Status / open input |
|---|---|---|---|
| `(1−ρ)/3 ≈ 0.16667` | `production_good_ladder_reach` | RS granularity ladder: at radius `j/n` there are `≤ j` bad scalars provided `3(j−1)+k ≤ n` (from the distance property `rsCode_noWeightLE`, `m+k ≤ n`). Reach `j_max = ⌊(n−k)/3⌋+1`. The factor `3` (not `2`) is the price of the *exact* granularity determination in `mcaDeltaStar_eq_granularity` (two `noWeightLE` calls). | **UNCONDITIONAL, LANDED.** This is the current floor. |
| Johnson `1 − √ρ ≈ 0.29289` | `production_good_johnson_of_packageSupply` (`ProductionRegimeBracket.lean`) | BCIKS20/Hab25 Johnson-lane funnel: every Johnson-range radius is good (`epsMCA ≤ ε*`, ¬pairJoint clause included — it is baked into `epsMCA`). | **CONDITIONAL** on the single named residual `CellPackageSupply` (`Hab25JohnsonPackageSupply.lean`) = [BCIKS20] Claim 5.7 per-cell §5 package + the numeric budget `johnsonBoundReal ≤ ε*`. Everything else in the chain is proven (`johnsonDischargeStatement_of_packageSupply`). |

**Mutual-CA at Johnson (the `¬pairJoint` question).** YES — the in-tree Johnson lane already proves
the *full* MCA statement at Johnson (goodness = `epsMCA ≤ ε*`, and `epsMCA`/`mcaEvent` carry the
`¬pairJointAgreesOn` clause intrinsically). There is no separate "pairJoint patch" needed: the
mutual-CA `¬pairJoint` clause is inside the very error the Johnson lane bounds. The sole gap
between the ladder floor `0.16667` and the Johnson floor `0.29289` is `CellPackageSupply`.

**What it takes to push `0.16667 → 0.29289`:** discharge `CellPackageSupply` at the production
parameters (`n=2^30`, `k=2^29`, `m ≥ 12`, `δ` in the Johnson range) and feed
`production_good_johnson_of_packageSupply`. This is the [BCIKS20] Claim 5.7 construction (produce
the pinning centre `x₀`, the `Y`-root divisor `H`, and the matching sets over a large cell). No
in-tree BCIKS "correlated-agreement at Johnson" theorem is currently discharged unconditionally —
`CellPackageSupply` is precisely that missing input, formalized as one Prop.

## 6. The three sharpest next theorems (ranked)

1. **[FLOOR, highest value] Discharge `CellPackageSupply` at production shape → floor `0.16667 → 0.29289`.**
   Precise: prove
   `∀ n k m (…), 2≤k → k+1≤n → 12≤m → δ≤1 → CellPackageSupply domain k δ (killBudget n k m)`
   at the prize parameters, then instantiate `production_good_johnson_of_packageSupply` to land
   `firstPrime_rateHalf_ladder_floor_johnson : (johnsonRadius) ≤ mcaDeltaStar (evalCode g 2^30 (2^29−1)) ε*`.
   Effect: closes the entire FLOOR sub-strip `[0.16667, 0.29289]` and brings the unconditional
   bracket to `[Johnson, 1/3]`. This is the single most valuable theorem on the board — it is the
   one named residual and it moves the floor by `0.126`.
   **SYZ8 update (2026-07-10):** the residual is re-based on its strictly-smaller disc-locus
   form `CellPackageSupplyDiscLocus` (`Frontier/_SYZ8CellPackageSupply.lean`):
   `cellPackageSupply_of_discLocus` proves disc-locus supply ⟹ `CellPackageSupply`, and
   `production_good_johnson_of_discLocusSupply` /
   `johnsonDischargeStatement_of_discLocusSupply` re-wire the floor jump off the smaller
   residual. What an implementor must produce is now: per large cell, the surface data
   (`H`, `x₀`, degree grading, `Ppoly`), the Y-root divisor `w`, ONE nonzero `disc` with a
   single base + separability certificate over its non-vanishing locus, and disc-locus
   matching/heavy sets — the [BCIKS20] Claim 5.7 production, genuinely open. See
   `docs/kb/deltastar-466-syz8-cell-package-supply-2026-07-10.md`.

2. **[CEILING, formalize the barrier] The degenerate-channel rank-budget wall `δ_channel ≥ (1−ρ)/(2−ρ)`.**
   **DONE (SYZ9, 2026-07-10):** landed axiom-clean in
   `Frontier/_SYZ9ChannelRankWall.lean` (`channel_master`, `channel_radius_gt_infimum`,
   `production_channel_safe`: rate-1/2 safe radius `≤ 357913941/2^30 < 1/3`; channel reach
   `(357913941/2^30, 358612991/2^30] ⊆ (1/3,1]` with SYZ6). See
   `docs/kb/deltastar-466-syz9-channel-rank-wall-2026-07-10.md`. Original target text below.
   Precise: prove that any stack whose certified `mcaEvent`-bad count exceeds the budget through the
   syzygy channel (i.e. via the `G87McaEventSyndromeBridge` degenerate-subset structure) has radius
   `δ ≥ (1−ρ)/(2−ρ)`; equivalently `epsMCA C δ > ε*` witnessed by ≥ `D` degenerate subsets forces
   `δ·(2−ρ) ≥ 1−ρ`. Effect: converts §2's arithmetic + §4's empirical starvation into a Lean
   theorem that the SYZ channel *cannot* enter `[Johnson, 1/3]`, cleanly isolating the decisive
   strip as "genuinely-new-construction-required." Builds directly on the landed
   `_G87McaEventSyndromeBridge` + the SYZ2/SYZ3 pencil/witness machinery (all axiom-clean).

3. **[CEILING/CORE, decide the strip] Channel-completeness OR a strip-radius bad construction.**
   Two mutually exclusive precise targets, whichever is true:
   (a) *Good side (expected):* prove every radius in `[Johnson, 1/3)` is good at production —
   `∀ δ, Johnson ≤ δ < 1/3 → epsMCA (evalCode g 2^30 (2^29−1)) δ ≤ ε*` — extending the Johnson
   funnel from `1−√ρ` up to `1/3`; this pushes the floor (hence `δ*`) to `1/3` and, with #2,
   pins `δ* = 1/3`. This is the hard BCIKS proximity-gap statement beyond Johnson.
   (b) *Bad side (the empirical scan predicts NO):* exhibit a non-degenerate-subset stack certifying
   `> ε*·q` bad scalars at some `δ ∈ (Johnson, 1/3)` — `∃ stack, epsMCA … δ > ε*` with `δ < 1/3`.
   Combined with #2 this would drop the ceiling into the strip. The §4 scan found none across A/
   NEAR/MIX/RAND at `n∈{32,64}` (CONJECTURE: (b) is impossible, i.e. (a) holds).

## Cross-references
- SYZ arc: SYZ1 (`_SYZ2PredecessorCapRefutationCore`, refutation), SYZ2/SYZ3 (pencil/witness),
  SYZ4 (`_SYZ4DegenerateChannelCeiling.lean`, `11/32−2^-30`), SYZ5
  (`_SYZ5RateQuarterChannelCeiling.lean`, rate-1/4 no-go), SYZ6
  (`_SYZ6FinerGradingCeiling.lean`, `358612991/2^30`).
- Floor: `ProductionRegimeBracket.lean`, `GranularityLadderRS.lean`,
  `Hab25JohnsonPackageSupply.lean` (residual `CellPackageSupply`).
- Bracket assembly: `Frontier/_PrizeShapeRateHalfBracket.lean`.
- Probe: `scripts/probes/probe_syz7_strip_scan.py` (this round);
  `scripts/probes/probe_syzygy_configuration_bad_counts.py` (SYZ1 harness, `m=2` only).
- Issue #466 / #507. Tag SYZ7.
