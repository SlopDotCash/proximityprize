# wf407 / T13-dyadic — per-level deviation `δ_i` of the 2-adic Gauss-period cocycle

**Date:** 2026-06-14 · **Thread:** 407-T13 · **Verdict: REFUTED** (the `O(1/i)` decay-rate
hypothesis is false; the route collapses onto the proven √(n log m) EVT / generalized-Paley wall).

## The question

The prize floor is `B = max_{b≠0} ‖η_b(μ_n)‖`. Up the 2-adic tower `n = 2^i`, the worst period
`M_i := B(μ_{2^i})` satisfies the EXACT parallelogram cocycle (in-tree
`Sweep_A12_PhaseAlignmentTower.gaussPeriod_tower_parallelogram`):

```
‖A + B‖² + ‖A − B‖² = 2(‖A‖² + ‖B‖²),    A = η_{b}(μ_{n/2}),  B = η_{bz}(μ_{n/2}).
```

The per-level **doubling ratio** at the worst frequency `b*` is `ρ_i := ‖A+B‖²/(2 M_{i-1}²)` and the
per-level **deviation** is `δ_i := ρ_i − 1` (equivalently `d_i := log₂ ρ_i`). A *constant* positive
excess `d_i → c > 0` compounds: `M_a² ≥ 2^a·2^{ca} = n^{1+c}` — a **power overshoot** of the worst
period = FATAL (this is the census's "constant excess → power `n^{c(δ)}`, proven fatal"). The route's
hope: `δ_i` (or `d_i`) **decays like `O(1/i)`**, so `Σ d_i ~ C log a = C log log n` = poly-log, and the
floor `B = O(√(n log n))` survives via the cocycle.

> NOTE: TOWER-2 decoupling and `M(2n)² ≤ 2 M(n)²` are already REFUTED (ratios to 3.86); not redone.
> T13 is the *finer* question: the decay **rate** of the deviation, not the crude bound.

## Method

Two EXACT probes (numpy, no sampling), four **non-Fermat** primes (odd part of `(p−1)/n > 1`, the
#400 Fermat trap excluded), tower depths up to **14 levels** (`i = 6..20`):

- `scripts/probes/wf407_T13-dyadic_deviation_decay.py` — `M_i`, `ρ_i`, `d_i`, `c_i := M_i²/(n ln m)−1`.
- `scripts/probes/wf407_T13-dyadic_cocycle_cos_persistence.py` — the child periods `A,B` at the SAME
  `b*`, the cocycle multiplier `r_i = M_i/max(|A|,|B|)`, the alignment `cos_i = Re(A·conj B)/(|A||B|)`,
  the normalized cross term `δ_x = 2Re(A·conj B)/(|A|²+|B|²)`, and the split residual `|(A+B)−η_{b*}(μ_n)|`
  (≤ 8e-13 everywhere — confirms `A+B = η_{b*}(μ_n)` exactly).

## Results (decisive)

**(1) `δ_i` does NOT decay `O(1/i)` — it is constant-amplitude OSCILLATING.**
The decay-verdict line: `decaying=NO` for 3/4 primes (`slow` for the 4th). The `O(1/i)` diagnostic
`|d_i|·i` (flat ⟺ `d_i = O(1/i)`) instead **grows** with depth — tail means `5.9, 4.2, 10.3, 14.6`
with large std. Deep-level `|d_i|` (`0.74, 0.16, 0.71, 0.97`) is as large as shallow `|d_i|`.

| p | p−1 | depth | `d_i` deep tail | `|d_i|·i` tail mean | decay |
|---|---|---|---|---|---|
| 12289 | 2¹²·3 | i=2..12 | …−0.57,−0.63,−0.74 | 5.88 | **NO** |
| 40961 | 2¹³·5 | i=2..13 | …−0.09,−0.67,−0.16 | 4.20 | slow |
| 786433 | 2¹⁸·3 | i=5..18 | …+0.19,−0.67,−0.71 | 10.29 | **NO** |
| 3145729 | 2²⁰·3 | i=6..20 | …−1.29,+0.91,+0.97 | 14.59 | **NO** |

**(2) But the cumulative `Σ d_i` is BOUNDED and trends NEGATIVE** (ends `−1.6, −0.6, −3.8, −3.2`):
the worst period grows **at or below** the pure-Gaussian doubling rate. There is **no positive
accumulating excess** that an `O(1/i)` decay was needed to tame — the route's premise is *misframed*.
Correspondingly `c_i = M_i²/(n ln m) − 1` stays `O(1)` and oscillating (never a power-law drift) —
`M_i` tracks the proven √(n log m) law with a bounded oscillating constant.

**(3) Phase alignment `cos_i = +1.0000` EXACTLY at every non-degenerate level** (389-T03), persistent
all the way up the tower at `b*` — *stronger* than the prior DISPROOF_LOG note (which saw degradation
for generic cofactors when tracking the level-`i−1` maximizer, not the level-`i` `b*`). Yet `cos=+1`
does **not** force super-doubling: the level-`i` worst children `A,B` are themselves **sub-maximal** at
level `i−1` (`|A|²+|B|² < 2 M_{i-1}²`, i.e. `r_i < 2`, `δ_x` oscillates `0.3–1.0`). Coherent addition
of sub-maximal children keeps `ρ_i` oscillating *across* the Gaussian baseline 1, not above it. This
is the exact mechanism: **the worst frequency relocates between levels**, so the cocycle never
accumulates a positive excess.

**Fermat control** (`p = 65537`, `p−1 = 2¹⁶`): the degenerate `m → 1` collapse (`d_i → −15` at the
top), as expected; excluded from the verdict.

## Lean brick (axiom-clean)

`Research/ProximityPrize/Frontier/WF407_T13DyadicDeviation.lean`
(`[propext, Classical.choice, Quot.sound]`):

- `doublingRatio_eq` — exact `‖A+B‖² = (‖A‖²+‖B‖²) + 2·Re(A·conj B)`.
- `cross_term_identity` — `‖A+B‖² − ‖A−B‖² = 4·Re(A·conj B)`.
- `deviation_decomp` — `δ_i = (crossExcess + subMaxGap)/(2 M_{i-1}²)`, sign-indefinite by inspection.
- `deviation_negative_witness` / `deviation_not_sign_definite` — `decide`/`norm_num` rational
  countermodel from the probe (`p=786433, i=15`: `‖A+B‖² ≤ 311² < 2·370² ≤ 2 M₁₄²`) ⟹ `ρ₁₅ < 1`,
  `δ₁₅ < 0`: **no constant `c>0` lower-bounds `δ_i`** — the positive-excess premise is false.

## Verdict and what remains

**REFUTED:** `δ_i = O(1/i)` is false — `δ_i` does not decay (constant-amplitude oscillation,
`|d_i|·i` diverges) and is not even positively signed (`δ_i < 0` at many levels). The specific
"control the cocycle via `O(1/i)` decay" mechanism the route needed **does not exist**.

This is NOT a refutation of the floor. The floor `B = O(√(n log m))` survives — but for the
**already-known** reason: bounded EVT/Salem–Zygmund oscillation of the `m = (q−1)/n` Gauss periods
(`c_i = O(1)` oscillating), captured by `WorstPeriodLowerBound` / `SalemZygmundChaining` /
`GeneralizedPaleyRamanujan` — **not** by any cocycle decay. So the T13 route **collapses onto the
proven √(n log m) EVT / generalized-Paley wall** (faces 3↔4 of the open core). No new mechanism.

**Cross-path note for the next wave:** the persistent `cos_i = +1` at `b*` is real and exact, but it
is *self-fulfilling* (the untwisted branch IS the maximum by definition of `b*`), so it carries no
descent content — confirming and sharpening DISPROOF_LOG `### (2)`. The genuine open object is
unchanged: bound the worst of the `m` Gauss-period oscillations (the EVT max-of-`m`-sub-Gaussians),
which is the Paley/BGK √-cancellation wall.

## Artifacts
- `scripts/probes/wf407_T13-dyadic_deviation_decay.py`
- `scripts/probes/wf407_T13-dyadic_cocycle_cos_persistence.py`
- `Research/ProximityPrize/Frontier/WF407_T13DyadicDeviation.lean`
