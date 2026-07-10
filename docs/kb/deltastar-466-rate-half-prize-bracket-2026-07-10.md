# Exact-rate-half prize bracket and one-rung residual (2026-07-10)

## Result

`Frontier/_PrizeShapeRateHalfBracket.lean` gives an unconditional concrete bracket for
the `n = 2^30`, `k = 2^29` Reed--Solomon code over each of the two certified prize-shaped
prime fields:

```text
178956971 / 2^30 <= deltaStar <= 31/64.
```

Numerically this is

```text
0.16666666697710752 <= deltaStar <= 0.484375.
```

The upper endpoint is new at this concrete field scale.  The earlier uniform quotient
wrapper reserved enough interpolation support for every field below `2^256` and therefore
started at quotient size `256`.  Retaining the actual value of `floor(p/2^128)` makes the
size-`64` quotient sufficient.

This is a bracket, not a completed prize pin.  The file isolates the exact one-Hamming-rung
incidence statement which would make `31/64` an equality.

## Exact arithmetic

Put `Q = 2^128`, `n = 2^30`, and use the quotient parameters

```text
s = 64,       m = 2^24,       r = 33.
```

Then

```text
s*m = n,
(r-1)*m = 2^29 = k,
1-r/s = 31/64,
choose(64,33) = 1777090076065542336.
```

The rounded second-moment construction needs `M = floor(p/Q)+3` quotient supports.
The certified fields have different exact budgets:

| field | `floor(p/Q)` | rounded `M` | predecessor cap needed |
|---|---:|---:|---:|
| first prime | `2^30 = n` | `1073741827` | `n` |
| second prime | `2^31 = 2n` | `2147483651` | `2n` |

Both rounded targets are tiny compared with `choose(64,33)`.  The immediately preceding
dyadic quotient is genuinely too short:

```text
choose(32,17) = 565722720 < n+3 < 2n+3.
```

Thus size `64` is the first available adjacent dyadic quotient rung for this exact
second-moment mechanism.

## Formal theorem inventory

The new axiom-clean module proves:

```text
firstPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour
secondPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour

firstPrime_rateHalf_ladder_floor
secondPrime_rateHalf_ladder_floor

firstPrime_rateHalf_deltaStar_bracket
secondPrime_rateHalf_deltaStar_bracket
```

It also gives the exact conditional closures

```text
firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count
secondPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count
```

with count budgets `n` and `2n`, respectively.  A reusable theorem
`latticeBoundary_le_mcaDeltaStar_of_predecessor_good` proves that one good Hamming
predecessor fills the entire open real interval below the next lattice point.

All printed theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`.

## The exact remaining rung

The boundary error count and its predecessor are

```text
e0     = 31 * 2^24     = 520093696,
e_prev = e0 - 1        = 520093695,
delta_prev = e_prev / 2^30
           = 31/64 - 1/2^30
           = 0.4843749990686774.
```

For the first field it is enough to prove, for every stack `(u0,u1)`,

```text
#{gamma : mcaEvent(delta_prev,u0,u1,gamma)} <= 2^30.
```

For the second field the corresponding exact count is `<= 2^31`.  No asymptotic
rounding or continuity assertion remains in these connectors.

The projective quotient-ball substrate gives an equivalent geometric reading.  Let `H`
be the `k x n` dual Vandermonde frame, let `P` be a syndrome pencil, and for a coordinate
support `T` let `B_T = span(H_T)`.  A proper bad slot is exactly a projective point of
`P intersect B_T` with `P` not contained in `B_T`.  Hence the first-field residual is the
explicit bound `n` on the number of distinct proper intersection points over all
`|T| <= e_prev`; the second-field residual permits `2n`.

### Locator-recurrence form of the binding layer

At the binding support size `|T| = e_prev`, write the locator

```text
Lambda_T(Z) = product_{x in T} (Z-x).
```

The syndrome has `k=32m` consecutive moments.  A support of size `31m-1` therefore leaves

```text
k - |T| = m+1
```

independent recurrence equations.  For a syndrome pencil `z0 + gamma*z1`, form the two
`(m+1)`-vectors obtained by applying those recurrence equations to `z0` and `z1`.
The support contributes one proper projective label precisely when these vectors are
dependent but not both zero.  The target is to bound the number of distinct resulting
ratios, not the number of locators.

This exposes the sharp phase transition.  At the bad quotient boundary `|T|=31m`, only
`m` recurrence equations remain; the predecessor adds exactly one equation.  A useful
proof must exploit that extra equation together with `Lambda_T | (Z^n-1)`.  Ordinary MDS,
dual generalized weights, and even order-two higher-MDS data do not count these distinct
rank-one ratios; `_ProjectiveDualWeightNoGo.lean` formally rules out that shortcut.

## Red-team audit

### 1. The naive half-predecessor cap is false

The theorem

```text
firstPrime_rateHalf_not_halfPredecessor_badCount_le_length
```

proves that an all-stack `n`-scalar cap at the last lattice point below `1/2` cannot hold.
If it did, monotonicity would make `31/64` good, contradicting the unconditional quotient
spread.  The rate-half target must be the predecessor of `31/64`, not the predecessor of
`1/2`.

### 2. A tempting 34-whole-fiber reduction is invalid

The boundary witness uses words constant on the `m`-point fibers of `X -> X^m`, so it is
tempting to say that `33m+1` agreements require 34 whole quotient fibers.  That argument is
false for the universal good side: the competing codeword is an arbitrary polynomial of
degree `<32m`, not a polynomial in `X^m`.

Indeed it has the radix decomposition

```text
q(X) = sum_{b=0}^{m-1} X^b Q_b(X^m),       deg Q_b < 32.
```

The `b>0` components can create partial-fiber agreements.  Any proof which silently
restricts the decoding codeword to `Q_0(X^m)` loses the worst-case stack and is unsound.

### 3. Exact toy falsifier

`scripts/probes/probe_rate_half_quotient_predecessor.py` enumerates every support of size at
most five for the proper-subgroup analog

```text
RS[16,8] over mu_16 in F_4001,
(s,m,r)=(8,2,5),
boundary agreement 10, predecessor agreement 11.
```

It certifies:

```text
boundary quotient scalars                 56 = choose(8,5)
same quotient pencil at predecessor        0 proper points
independent four-anchor Schubert pencil    12 proper points
independent five-anchor Schubert pencil    13 proper points
candidate length cap                       16
```

Thus the explicit quotient stack dies completely one step earlier in this clean toy lift,
while other pencils still produce a nontrivial predecessor census.  This supports, but does
not prove, a one-rung phase transition.  No claim of exhaustive line search is made.

## Good-side audit

The lower endpoint `178956971/2^30` is the full unconditional granularity-ladder reach

```text
j = floor((n-k)/3)+1 = 178956971.
```

The other currently landed unconditional consumers do not improve it at rate one half:

- the quarter/interleaved unique-decoding radius is asymptotically `1/8`;
- half-Johnson is asymptotically `(1-sqrt(1/2))/2`, about `0.146447`;
- the full below-UDR `n/p` statement still consumes the named
  `WindowRationalLinear` residual;
- generic all-witness and puncture bounds have superlinear or exponential count budgets at
  this predecessor.

The second field's larger `2n` normalized budget does not extend the ladder's arithmetic
radius condition, so its present unconditional floor is the same.

## Next proof target

The most economical exact target is now:

> For every rank-two syndrome pencil of the certified smooth `RS[2^30,2^29]` code, the
> union of the proper rank-one intersections indexed by divisors of `Z^n-1` of degree at
> most `31*2^24-1` has at most `n` distinct projective labels (first field), or at most
> `2n` labels (second field).

The locator-recurrence presentation should be preferred to a raw support count: it retains
the one extra predecessor equation and the dyadic divisor structure simultaneously.  A
successful argument must control distinct ratios across many locators; counting locators,
using only generalized weights, or collapsing to whole quotient fibers is provably too
coarse.

## Validation

The Lean module passes both the fast cone check and a real locked project build.  The probe
above runs in under a second and checks its exact finite-field certificates by assertion.
