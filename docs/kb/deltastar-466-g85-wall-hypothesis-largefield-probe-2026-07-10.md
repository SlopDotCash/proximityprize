# G85 large-field probe of the rate-half predecessor-count wall hypothesis (2026-07-10)

Follow-up (issues #466/#507) to the G84 small-scale red-team probe
(`docs/kb/deltastar-466-g84-wall-hypothesis-smallscale-probe-2026-07-10.md`), which refuted
every small-field ANALOGUE of the wall hypothesis of
`firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count`
(`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapeRateHalfBracket.lean`) and
predicted the refutations are small-field artifacts that collapse once
`p >> C(n,t)^{1/(t-k)}`. This probe tests that prediction at G84's stated faithful next cell:
`n = 64, k = 32, t = 34` (`t-k = 2`; both G84 translations coincide, `64 | n`), with sampled
gamma and a certified constructive channel, across primes bracketing the predicted threshold.

Probe: `scripts/probes/probe_rate_half_predecessor_count_largefield.py`
(deterministic seeds, exact bigint/int64 arithmetic; ~25 min single-core).

## Thresholds, exactly

```
C(64,34) = 1620288010530347424                (~2^60.49)
p*(64)      := C(64,34)^{1/(t-k)} = isqrt(C(64,34)) = 1272905342   (~2^30.25)
                 -- below p*: heuristic per-gamma bad fraction C/p^2 >= 1 (ALL gammas bad)
p_count(64) := C(64,34)/64 = 25317000164536678                     (~2^54.49)
                 -- below p_count: heuristic bad COUNT C/p > budget n even with fraction < 1
n=32 secondary (k=16, t=18, same margin shape t-k=2):
C(32,18) = 471435600;  p*(32) = 21712 (~2^14.4);  p_count(32) = 14732362 (~2^23.8)
```

## Method (exact skeleton)

- Per t-subset `S`, "some codeword agrees with the line `u0 + gamma*u1` on all of S" is the
  two GRS parity checks (dual of RS_k on `t = k+2` points, multipliers
  `c_i = 1/prod_{l != i}(x_i - x_l)`); the condition on gamma is AFFINE: `a + gamma*b = 0`
  in `F^2`, so each subset carries at most ONE candidate gamma (or all of F when `a = b = 0`).
- **Constructive (importance) channel**: enumerate a pool of t-subsets (2*10^6 via numpy int64
  when `p < 2^31`, 2*10^4 bigint otherwise), solve for the candidate gamma per subset, then
  FULLY verify `mcaEvent` (interpolate `w`, agreement set `A`, `|A| >= t`, NOT pairJoint).
  Every verified gamma is a certified witness => **rigorous lower bound** on the bad count.
- **Uniform sampling**: 10^4 seeded gammas per stack, tested through the same reduction
  (affine-in-gamma => pool-relative badness = candidate-set membership + full verification).
- **Planted channel**: choose `r` distinct gammas and subsets `S_j`, solve the homogeneous
  system `H_{S_j}(u0|S_j) + gamma_j H_{S_j}(u1|S_j) = 0` (2r equations, 2n unknowns). The
  kernel always contains the 2k-dim codeword-pair space (never bad), so non-trivially bad
  stacks exist iff `rank < 2(n-k)`: **linear-channel law**
  `r_max = 2(n-k)/(t-k) - 1` (= 31 at n=64, 15 at n=32, ~2^30/(2^24+1) ~ 63 at production).
- Stacks: G84 battery (random, codeword-pair, near-codeword, split-codeword, monomial-k-k1,
  subgroup-supported, spike) + planted at `r in {r_max/2, r_max, r_max+1, r_max+2}`.
- Every REFUTED cell's witnesses are individually recounted by a second interpolation path
  (different node set); all recounts matched (assert-guarded).

## Collapse curve (worst stack per cell; certified = rigorous lower bound; heuristic = C(n,t)/p)

| n | tag | p | log2 p | pool M | certified LB (worst) | worst stack | sampled frac | heuristic count | budget | verdict |
|---|---|---|---|---|---|---|---|---|---|---|
| 32 | p*/8 | 2753 | 11.43 | 2000000 | 132 (cap) | random-0 | 0.2235 | 1.712e+05 | 32 | REFUTED-CERTIFIED |
| 32 | p*/2 | 11329 | 13.47 | 2000000 | 132 (cap) | random-0 | 0.0152 | 4.161e+04 | 32 | REFUTED-CERTIFIED |
| 32 | p* | 22273 | 14.44 | 2000000 | 109 | random-4 | 0.0057 | 2.117e+04 | 32 | REFUTED-CERTIFIED |
| 32 | 2p* | 43457 | 15.41 | 2000000 | 74 | planted-r15 | 0.0021 | 1.085e+04 | 32 | REFUTED-CERTIFIED |
| 32 | 8p* | 173729 | 17.41 | 2000000 | 27 | planted-r15 | 0.0001 | 2.714e+03 | 32 | CONSISTENT |
| 32 | 64p* | 1389569 | 20.41 | 2000000 | 16 | planted-r15 | 0.0000 | 3.393e+02 | 32 | CONSISTENT |
| 32 | p_count | 14732513 | 23.81 | 2000000 | 15 | planted-r15 | 0.0000 | 3.200e+01 | 32 | CONSISTENT |
| 32 | 2^40 | 1099511627873 | 40.00 | 20000 | 15 | planted-r15 | 0.0000 | 4.288e-04 | 32 | CONSISTENT |
| 64 | p*/8 | 159113281 | 27.25 | 1000000 | 31 | planted-r31 | 0.0000 | 1.018e+10 | 64 | CONSISTENT |
| 64 | p*/2 | 636452737 | 29.25 | 1000000 | 31 | planted-r31 | 0.0000 | 2.546e+09 | 64 | CONSISTENT |
| 64 | p* | 1272907073 | 30.25 | 1000000 | 31 | planted-r31 | 0.0000 | 1.273e+09 | 64 | CONSISTENT |
| 64 | 2p* | 2545811969 | 31.25 | 20000 | 31 | planted-r31 | 0.0000 | 6.365e+08 | 64 | CONSISTENT |
| 64 | 8p* | 10183243009 | 33.25 | 20000 | 31 | planted-r31 | 0.0000 | 1.591e+08 | 64 | CONSISTENT |
| 64 | 2^54 | 18014398509485249 | 54.00 | 20000 | 31 | planted-r31 | 0.0000 | 8.994e+01 | 64 | CONSISTENT |
| 64 | p_count | 25317000164539969 | 54.49 | 20000 | 31 | planted-r31 | 0.0000 | 6.400e+01 | 64 | CONSISTENT |
| 64 | 2^57 | 144115188075856001 | 57.00 | 20000 | 31 | planted-r31 | 0.0000 | 1.124e+01 | 64 | CONSISTENT |
| 64 | 2^80 | 1208925819614629174707521 | 80.00 | 20000 | 31 | planted-r31 | 0.0000 | 1.340e-06 | 64 | CONSISTENT |

"132 (cap)" = verification cap (budget + 100) hit, true certified count larger. All 4
REFUTED cells were recounted witness-by-witness on an independent interpolation path.
"CONSISTENT" = no violation found by the pool + planted + sampled channels (coverage
`M/p` per cell in the probe output; it is vanishing at large p, see honest scope).

## Did the predicted threshold match?

**Yes, at the measured scale (n=32), to within the certification frontier.** Certified
refutations persist through `2 p*` and are gone by `8 p*`; the certified worst count decays
`132(cap) -> 132(cap) -> 109 -> 74 -> 27 -> 16 -> 15` across `p*/8 -> p_count`, i.e. the
saturation regime ends where `C/p^2 ~ 1` predicts, and by `p_count` (where the heuristic
count C/p exactly equals the budget 32) the certified count has landed on the planted-channel
floor `r_max = 15`, where it stays flat through `2^40`. Two caveats keep this from being a
sharp measured crossing: (a) the certified channel is pool-limited (`~M/p` expected hits), so
between `8 p*` and `p_count` the true count likely still exceeds the budget (heuristic
2714 -> 32) without our being able to certify it; (b) at `n = 64` the pool coverage `M/p` is
already ~10^-2 at `p*/8`, so no sub-p* saturation could be certified at all — every n=64 cell
sits on the planted floor 31 <= 64 = budget, CONSISTENT at all magnitudes up to 2^80.

## New structural fact: the linear-channel planting law

The only bad-gamma production channel that survives `p >> p_count` is linear-algebraic, and
it is exactly capped: planting r distinct bad gammas needs a nonzero solution outside the
codeword-pair kernel, which exists iff `2r < 2(n-k)`. Verified on both cells and at every
prime magnitude (9/9 at n=64, 8/8 at n=32):

- n=32: `planted-r15` succeeds (rank 30), certified exactly 15; `r16/r17` UNPLANTABLE (rank 32 = 2(n-k)).
- n=64: `planted-r31` succeeds (rank 62), certified exactly 31; `r32/r33` UNPLANTABLE (rank 64 = 2(n-k)).

So the adversary's rigorous large-field floor is `2(n-k)/(t-k) - 1`, which is `< n` with
factor-2 headroom at these cells and `~ 2^30/(2^24+1) ~ 63 << 2^30` at production. (At
`p <= ~2 p*` the combinatorial channel piggybacks extra witnesses on planted stacks — e.g.
74 at n=32/2p* — which is why planted stacks are the worst family there too.)

## Honest analysis: what this evidences for production (and what it does not)

Production: `n = 2^30`, `k = 2^29`, `t - k = 2^24 + 1`, `P = 2^30*(2^128+192)+1 ~ 2^158`.
Extrapolating the first-moment law fitted by the measured curve
(`bad count ~ C(n,t) * p^{-(t-k)+1} + linear channel`):

- combinatorial channel: `log2(C(2^30, t) * P^{-(t-k)+1}) ~ 1.07e9 - 2^24 * 158 ~ -1.58e9` —
  astronomically negative (production sits ~10^8 binary orders of magnitude past its p_count);
- linear channel: capped at `~63 << 2^30` budget, and this cap is EXACT rank arithmetic,
  not a heuristic.

So everything measured here is consistent with the G84 prediction: the small-field
refutations are analogue artifacts, and in the faithful large-field/large-margin regime no
channel we can construct or certify comes anywhere near the budget. **This is evidence, not
proof**: the upper story (that the combinatorial channel really dies like its first moment,
i.e. that no stack correlates C(n,t) subsets far beyond independence) is exactly the open
wall; only the lower-bound side (certified witnesses, planting cap) is rigorous. A proof
would need a second-moment / eigenvalue argument in the `p >> C(n,t)^{1/(t-k)}` regime; a
refutation would need a construction beating the `2(n-k)/(t-k)` linear cap, which this probe
now shows cannot be a generic-rank planting.

Status: probe + docs only; no Lean changes; the production wall hypothesis of
`firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count` stays OPEN,
with the refutation surface narrowed (generic planting is dead; any counterexample must
create super-generic rank collapse or subset correlations).
