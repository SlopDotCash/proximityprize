# G84 red-team: small-scale probe of the rate-half predecessor-count wall hypothesis (2026-07-10)

Red-team falsification probe (issues #466/#505/#507) of the ONE open wall hypothesis of the
conditional production pin identified in the G82 audit
(`docs/kb/deltastar-466-g82-production-gate-audit-2026-07-10.md`):

`firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count`
(`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapeRateHalfBracket.lean`).

Probe: `scripts/probes/probe_rate_half_predecessor_count_small_scale.py`
(deterministic seeds, exact modular arithmetic; ~15 min single-core).

## The hypothesis, exactly

For EVERY stack `(u0, u1)` over `F_P`, `P = 2^30*(2^128+192)+1`, code
`C = evalCode g (2^30) (2^29 - 1)` (rate-1/2 RS on the smooth `2^30`-subgroup domain):

```
#{gamma : mcaEvent C (predecessorRadius (2^30) (31*2^24)) u0 u1 gamma} <= 2^30
```

`predecessorRadius n a = (a-1)/n`, so the radius is `31/64 - 2^-30` and the `mcaEvent`
size constraint `|S| >= (1-d)*n` is the integer agreement threshold

```
t = n - (a-1) = 33*2^24 + 1 = k + m + 1,   m := n/64 = 2^24.
```

`mcaEvent` (Errors.lean:216): some `S` with `|S| >= t` on which a codeword equals
`u0 + gamma*u1` AND `NOT pairJointAgreesOn C S u0 u1`. Exact computational reduction
(proved in the script header): `gamma` bad iff some codeword `w` with agreement set
`A_w` of size `>= t` has `NOT pairJointAgreesOn C A_w u0 u1`.

## Translation table (production -> small scale)

| quantity | production | small-scale analogue |
|---|---|---|
| n | `2^30` | 8, 16, 32, 64 |
| k | `2^29` | `n/2` |
| field | `P = 2^30*c + 1`, `c = 2^128+192` | smallest primes `p = n*c + 1` (several per n) |
| domain | smooth `2^t` subgroup `<g>`, `ord(g)=n` | same (`g = a^((p-1)/n)`, order exactly `n`) |
| radius | `(31*2^24 - 1)/2^30` | T-literal: largest lattice point `< 31/64`; T-structural: `(k-m-1)/n`, `m = max(1, n/64)` |
| threshold t | `k + m + 1`, `m = 2^24` | T-literal: `k+1` for n in {8,16,32}, 34 at n=64; T-structural: `k+2` |
| budget | `2^30 = n` (2n second field) | `n` |

Degeneracy warning: for `n < 64` the literal lattice predecessor of `31/64` COINCIDES
with the predecessor of `1/2` (`t = k+1`) — the rung the Lean file itself refutes at
production (`firstPrime_rateHalf_not_halfPredecessor_badCount_le_length`). `n = 64`
(`t = 34`, both translations coincide, `64 | n`) is the smallest faithful cell.

## Results (worst stack per cell; EXACT = full C(n,k)-subset codeword enumeration,
SAMPLED = 4000-subset candidate pool, count is then a lower bound)

| n | p | translation | t | mode | worst count | worst stack | budget | verdict |
|---|---|---|---|---|---|---|---|---|
| 8 | 17 | literal | 5 | EXACT | 17 | random-0 | 8 | REFUTED-AT-ANALOGUE |
| 8 | 17 | structural | 6 | EXACT | 4 | split-codeword-5 | 8 | SURVIVES |
| 8 | 41 | literal | 5 | EXACT | 40 | monomial-k-k1 | 8 | REFUTED-AT-ANALOGUE |
| 8 | 41 | structural | 6 | EXACT | 4 | split-codeword-4 | 8 | SURVIVES |
| 8 | 73 | literal | 5 | EXACT | 46 | random-12 | 8 | REFUTED-AT-ANALOGUE |
| 8 | 73 | structural | 6 | EXACT | 4 | split-codeword-1 | 8 | SURVIVES |
| 16 | 17 | literal | 9 | EXACT | 17 (= p, all scalars) | random-0 | 16 | REFUTED-AT-ANALOGUE |
| 16 | 17 | structural | 10 | EXACT | 17 (= p) | random-0 | 16 | REFUTED-AT-ANALOGUE |
| 16 | 97 | literal | 9 | EXACT | 97 (= p) | random-0 | 16 | REFUTED-AT-ANALOGUE |
| 16 | 97 | structural | 10 | EXACT | 68 | split-codeword-4 | 16 | REFUTED-AT-ANALOGUE |
| 16 | 113 | literal | 9 | EXACT | 113 (= p) | random-0 | 16 | REFUTED-AT-ANALOGUE |
| 16 | 113 | structural | 10 | EXACT | 68 | random-8 | 16 | REFUTED-AT-ANALOGUE |
| 32 | 97 | literal | 17 | SAMPLED | 97 (= p) | random-0 | 32 | REFUTED-AT-ANALOGUE |
| 32 | 97 | structural | 18 | SAMPLED | 97 (= p) | random-0 | 32 | REFUTED-AT-ANALOGUE |
| 32 | 193 | literal | 17 | SAMPLED | 193 (= p) | random-0 | 32 | REFUTED-AT-ANALOGUE |
| 32 | 193 | structural | 18 | SAMPLED | 193 (= p) | random-0 | 32 | REFUTED-AT-ANALOGUE |
| 64 | 193 | both (t=34) | 34 | SAMPLED | 193 (= p) | random-0 | 64 | REFUTED-AT-ANALOGUE |

Every over-budget witness was independently recounted by a second (slow-path, pure-Python)
implementation; all recounts match exactly. Smallest exact refutation witness
(n=8, p=17, g=9, t=5, budget 8, all 17 scalars bad):

```
u0 = [12, 3, 12, 8, 14, 10, 10, 3]
u1 = [15, 1, 3, 14, 11, 3, 3, 11]
```

Faithful-cell witness (n=64, p=193, g=125, t=34, budget 64, all 193 scalars bad): the
FIRST random stack tried (`random-0`, seed `46684-64-193-literal-stacks`); full vectors in
the script output. Adversarial structure was unnecessary — generic stacks over-shoot.

## Verdict and honest scope

1. **The hypothesis shape is NOT a scale-free structural fact about rate-1/2 smooth-domain
   RS.** At every small analogue with the production agreement margin collapsed to
   `m <= 2` (i.e. `t <= k+2`), a *generic* stack blows the `n`-scalar budget — usually
   every scalar in the field is bad. The only surviving cells are `n = 8` structural,
   where `C(8,6)/p < 1`.

2. **Why this does not refute production (first-moment scaling).** The expected number of
   codewords agreeing with a random line on `>= t` points is about `C(n,t) * p^{k-t}`,
   so the heuristic bad-scalar count is `~ C(n,t) * p^{k-t+1}`. Small scale:
   `p ~ poly(n)` and margin `t-k-1 <= 1`, so this is `>> n` — refutation is the *generic*
   outcome, consistent with the boundary result `epsMCA = C(n,k+1)/|F|`
   (`BoundaryGenericFarExact.lean`) and with the in-file half-predecessor refutation.
   Production: `p ~ n * 2^128` and margin `m+1 = 2^24 + 1`, so
   `log2(C(n,t) * p^{k-t+1}) <~ 2^30 - 2^24 * 158 ~ -1.6e9` — astronomically negative.
   The wall hypothesis lives strictly in the `p >> C(n,t)^{1/(t-k)}` regime and has NO
   small-field analogue at any `n` with `p = poly(n)`.

3. **What WOULD be evidence either way.** A faithful probe needs the margin and field to
   scale together: `p >~ C(n,t)^{1/(t-k-1)}`, e.g. `n = 64`, `t = 34` (margin 2) needs
   `p >> C(64,34) ~ 2^61` — outside exhaustive-gamma range but reachable by sampled-gamma
   Monte Carlo with structured stacks; that is the natural G84 follow-up. Until then the
   hypothesis is unsupported *and* unrefuted by small-scale evidence: these refutations
   are analogue-regime artifacts, and no small-n cell can certify production truth.

4. Sampled cells (n >= 32) report lower bounds on the count (candidate pool of 4000
   k-subsets + structured windows/strides); their refutations are valid, their
   hypothetical survivals would have been weak. All refutations here happened to be
   `count = p` saturations, far above any pool-coverage concern.

Status: probe + docs only; no Lean changes; the production wall hypothesis stays OPEN,
now with a sharpened understanding that any proof must exploit the `p ~ n*2^128`
large-field/large-margin regime, not a scale-free counting argument.
