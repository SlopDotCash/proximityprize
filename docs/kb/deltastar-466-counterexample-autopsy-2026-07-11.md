# Issue #466: autopsy of the (64, 16778497, 5) DCEnergy counterexample in census coordinates

Date: 2026-07-11 (UTC). Exact-integer computation (10.4M multisets, full depth census).

## Findings

At the only known DCEnergyBound counterexample (n = 64, p = 16778497, r = 5, excess
2.11×10^17 ≈ 1.2% of q·Wick):

1. **The rung-5 disjoint census PASSES easily**: `2q·fiber_55 = 0.09` of its budget
   (2q·Wick_5 + n^10). The fully-disjoint sector is healthy.
2. **The low-rung anchors PASS** (barely): rung-2 at ratio 0.984, rung-3 at 0.964.
3. **The failure mass is carried by the descent-visible depths**: per-depth anomalies at
   r = 5 are +0.117 (s=0), −0.000 (s=1), **+0.546 (s=2)**, +0.031 (s=3), **+0.269 (s=4)**,
   +0.049 (s=5) in units of q·Wick_5.
4. **Regime diagnosis**: this prime has n^4/q = 0.99997 — the rung-2 crossover
   (n^{2t} ≈ q·Wick_t) sits at t ≈ 2, and the observed failure at r = 5 is the accumulated
   descent of near-crossover structure. Nothing here contradicts the G133 tower: its budget
   gates are production-shape kernel facts (n = 2^30, q ≤ 2^160) and rungs ≤ 10 are
   explicitly anchors.

## Strategic consequence for production

Production (n = 2^30, q ≈ 2^158) has its crossover at rung t ≈ 5–6 (n^t vs q·(2t−1)!!
flips between t = 5 and 6) — inside the tower's anchor zone (t ≤ 10). The counterexample
mechanism — descent accumulation of near-crossover rung structure, with the disjoint census
healthy — identifies **the production anchors at t ≈ 5, 6 as the critical open objects**,
arguably ahead of the deep census family. Conversely: no known evidence points at the deep
(t ≥ 11) censuses; the only observed failure mode lives at the crossover.

## Honest scope

One prime, one rung fully decomposed; floating-point-free. No production claim. CORE
remains OPEN.
