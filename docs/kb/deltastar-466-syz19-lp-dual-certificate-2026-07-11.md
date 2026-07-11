# SYZ19: LP-dual certificate hunt for the rate-1/2 decisive strip (2026-07-11)

Status: **study/probe round (no new Lean landed).** Verdict is NEGATIVE-with-diagnosis:
no NEW all-stack dual certificate falls out of the currently-proven constraints. The only LP
that certifies `#bad <= budget` throughout the strip `(Johnson, 1/3)` is SYZ9's, and it does so
**only because the degenerate core is pinned at size `s = t`**. Freeing the core size — while
using per-family facts that are each individually a proven in-tree theorem — makes the LP
optimum exceed budget across the *entire* strip and even *below* Johnson, because the per-family
rank costs are treated as additive when they are physically sub-additive. That gap **names the
next theorem**. Issue #466 / #507. Tag SYZ19.

Probe: `scripts/probes/probe_syz19_lp_dual_certificate.py` (exact `Fraction`; single-resource
simplex = exact ratio scan). Empirics reused from `scripts/probes/probe_syz7_strip_scan.py`
(fully `mcaEvent`-verified certified counts).

## The witness-profile LP and its theorem provenance

A **degenerate family** = a codeword pair `(v0,v1)` with a shared core `C`, `|C| = s`, on which
both `u0|C` and `u1|C` are codeword restrictions. Per family, three proven facts:

| Quantity | Value | In-tree theorem(s) |
|---|---|---|
| rank cost (syndrome pairs) | `s - k` (of `n - k` budget) | `_G86RankCollapseDichotomy.plantable_generic_cap`, `_G87McaEventSyndromeBridge` |
| yield (bad scalars) | `<= floor((n-s)/(t-s))` (`s<t`), `n-s` (`s>=t`) | SYZ2 `mcaEvent_pencil` (unique `gamma_x = -d0(x)/d1(x)`; off-core points partition among scalars; each bad scalar owns `>= t-s` of them), SYZ3 witness |
| cross-family overlap | `<= k-1` for independence (else codewords merge) | RS distance: two RS[n,k] codewords agreeing on `>= k` points are equal; `rsCode_noWeightLE` / CodeGeometry |
| aggregate rank budget | `sum_f (s_f - k) <= n - k` | `_G87McaEventSyndromeBridge` (2(n-k)-dim syndrome-pair space) |

Budget analogue `B = n` (production `eps* * q ~ n`).

Three LPs (all exact rational):
- **LPfix** — rank LP with the core PINNED at `s = t`. Optimum `= (n-k)(n-t)/(t-k) = R c / m`.
  This is exactly **SYZ9** (`channel_master`).
- **LPvar** — rank LP over VARIABLE core size `s` (single-resource knapsack; simplex).
  Optimum `= R * max_s yield(s)/(s-k)`.
- **LP3** — LPvar + Fisher cross-family overlap cap (`<= k-1`, convexity double count).

## Per-radius table (n=64, k=32, R=32, budget=64)

```
 t   delta   zone       m   c | empMax  LPfix(SYZ9)  LPvar  LP3  | budget
 39  0.3906  above-1/3  7  25 |   104      114.3      160   160  |  64   (killed)
 40  0.3750  above-1/3  8  24 |   100       96.0      128   128  |  64   (killed)
 42  0.3438  above-1/3 10  22 |    69       70.4       96    96  |  64   (killed)
 43  0.3281  STRIP     11  21 |    44       61.1       96    96  |  64
 44  0.3125  STRIP     12  20 |    42       53.3       64    64  |  64
 45  0.2969  STRIP     13  19 |    40       46.8       64    64  |  64
 46  0.2812  below-J   14  18 |    38       41.1       64    64  |  64
 48  0.2500  below-J   16  16 |    17       32.0       64    64  |  64
```
(n=32 cell identical in shape: LPfix dips below budget through the strip; LPvar/LP3 sit at/above
32 throughout.) `empMax` = SYZ7 fully-verified certified max over families A/NEAR/MIX/RAND.

## Verdicts

1. **LPfix = SYZ9 IS the dual certificate, and it decides the strip — but only for the pinned
   `s=t` channel.** For every STRIP row `LPfix < budget`; for every above-`1/3` row
   `LPfix > budget`; the crossover is at `(n-k)(n-t)/(t-k) = n`, i.e. `delta = (1-rho)/(2-rho)
   = 1/3`. Dual closed form (single rank constraint): value `= (n-k)(n-t)/(t-k)`, dual multiplier
   on the aggregate rank budget `y* = (n-t)/(t-k) = c/m`. This is exactly `channel_master` —
   SYZ19 confirms SYZ9 is the LP-dual optimum of the one-resource relaxation and finds **no
   richer certificate**.
   Empirically LPfix even upper-bounds the *NEAR* family throughout the strip and below
   (`empMax <= LPfix` for every `delta <= 1/3` row), though this is CONJECTURE — LPfix is only
   *proven* for `s=t`, and it FAILS as an upper bound above `1/3` (t=40: `empMax 100 > 96`).

2. **The all-stack (variable-core) LP is INSUFFICIENT: LPvar/LP3 exceed budget across the whole
   strip and below Johnson** (e.g. `96 > 64` at `t=43`, still `64 >= 64` down to `delta=0.25`),
   while empirics stay at `44, 42, 40, 38, 17`. The LP is loose by more than 2x versus what any
   stack achieves.

   **Impossible primal support (the diagnosis).** LPvar/LP3 both put all mass on the *minimal*
   core `s = k+1` (`s* = 17` at n=32, `33` at n=64): cost `1` each, so `D = R` independent
   families, each yielding `floor((n-k-1)/(t-k-1))`. The Fisher cross-overlap cap does **not**
   bind (`Dfish = 65 > Drank = 32` for size-33 cores). This profile — `R` distinct codeword
   pairs each agreeing with the *same* `(u0,u1)` on its own size-`(k+1)` core, cores mutually
   overlapping (32 size-33 sets in 64 points *must* overlap) — is not achievable: empirics realize
   only `~2` families' worth (`maxBad 44 ~ 2*(c+1)`), not `R = 32`.

## The missing constraint = the next theorem

The LP's single false assumption is that **per-family rank costs ADD**:
`sum_f (s_f - k) <= n - k`. That is the correct budget only when the `D` families' syndrome
systems are linearly *independent*. When cores share points (forced by pigeonhole for many
minimal cores), the shared coordinates produce shared parity rows, so the joint syndrome rank is
strictly **sub-additive**: `rank(union of family syndromes) << sum_f 2(s_f - k)`. The LP exploits
this by buying many rank-cheap overlapping cores that a single stack cannot host independently.

What is proven (`_G87McaEventSyndromeBridge`) is only the *aggregate* statement — the whole
stack lives in a `2(n-k)`-dim syndrome-pair space — which does not decompose additively across
overlapping cores, so it does not by itself forbid the impossible profile.

**Named residual (conjectured shape):** `degenerate_core_optimality` /
`joint_degenerate_rank_superadditive` — for any stack, the certified `mcaEvent`-bad count is
maximised by the `s = t` degenerate profile, i.e. no smaller-core family beats `R c / m`:
```
epsMCA C delta > eps*  certified through D degenerate cores (any sizes s_i >= k+1)
   ==>  #bad  <=  (n-k)(n-t)/(t-k).
```
Equivalently: `D` degenerate cores of sizes `s_i` with pairwise overlaps `o_ij` consume joint
syndrome rank `>= 2( |union C_i| - k )`, and the resulting bad-count LP has optimum `R c / m`.
This is precisely **SYZ7 §6 item (3)** (channel-completeness / strip decision), still open both
ways — SYZ19 sharpens *why* the easy LP relaxation cannot supply it: the missing physics is the
sub-additivity of joint syndrome rank under core overlap, not any of the four per-family facts
above (each of which is already a theorem).

## Honest scope

- No Lean landed. The probe uses ONLY the four proven per-family facts + the aggregate rank
  budget; every LP row is traceable to a named theorem (table above).
- SYZ9's certificate is re-derived as the one-resource LP dual and shown to be tight for the
  degenerate channel; SYZ19 adds no new certificate.
- Empirics are search evidence (n=32,64), not proof. The strip remains open both ways; SYZ19's
  contribution is the precise diagnosis that the obstruction to a *cheap* dual certificate is
  joint-rank sub-additivity, isolating the exact lemma a real certificate would need.

## Cross-references
- SYZ7 map: `docs/kb/deltastar-466-syz7-strip-map-2026-07-10.md` (§6 item 3 = the residual here).
- SYZ9 wall (the certificate SYZ19 re-derives): `docs/kb/deltastar-466-syz9-channel-rank-wall-2026-07-10.md`,
  `Frontier/_SYZ9ChannelRankWall.lean` (`channel_master`, `channel_radius_gt_infimum`).
- Rank machinery: `_G86RankCollapseDichotomy.lean`, `_G87McaEventSyndromeBridge.lean`.
- Probes: `scripts/probes/probe_syz19_lp_dual_certificate.py` (this round),
  `scripts/probes/probe_syz7_strip_scan.py` (empirics),
  `scripts/probes/probe_syzygy_configuration_bad_counts.py` (SYZ1 harness).
- Issue #466 / #507. Tag SYZ19.
