# Issue #466 G79S: primitive-padding saddle localization

Date: 2026-07-10

## Result

R369's production-facing target is the single saddle depth `r = ceil(log q)`.  If `J_s` counts
primitive disjoint cores of depth `s`, its maximal-common-padding argument gives the sector envelope

```text
W_s <= J_s * (r descFactorial s)^2 * n^(r-s).
```

G79S proves the exact arithmetic consumer for this envelope.  Define the last `s` odd Wick factors

```text
oddWickTail(r,s) = product_(i<s) (2(r-i)-1).
```

When `2s <= r+1`, every factor is at least `r`, hence

```text
r^s <= oddWickTail(r,s),       (r descFactorial s) <= r^s.
```

Therefore, if `J_s * r^s <= n^s`, then

```text
W_s <= oddWickTail(r,s) * n^r.
```

For a linear orbit budget `J_s <= C*n`, the sufficient condition becomes the transparent

```text
C * r^s <= n^(s-1).
```

At the nominal production parameters `n=2^30`, `r=110`, G79 kernel-checks the depth-two instance:
every single linear-size primitive orbit is absorbed by the last two Wick factors.

## Meaning for the saddle conjecture

This formally confirms the recovery mechanism observed at the shallow-exceptional cell
`n=32, p=21523361`: a bounded-depth orbit can violate shallow Wick bounds and still become
negligible at the saddle because factorial growth eventually pays for all of its padding.

It also narrows the genuine obstruction.  A counterexample to `FourthPowerSaddleDCEnergy` cannot be
carried by one fixed bounded-depth rotation orbit at production scale.  It must instead involve
either many primitive orbits at a fixed depth or primitive depth growing with `r`.

## Honest scope

G79S does not prove the combinatorial padding envelope; R369 currently records that step in prose.
It does not claim that the union of all primitive depth-`s` orbits has linear size.  Only each
individual free rotation orbit does.  The next exact theorem is a maximal-cancellation core
decomposition and padding surjection, followed by a quantitative orbit-count bound or a growing-core
tail estimate.  CORE remains open.

Lean file: `Frontier/_G79SPrimitivePaddingSaddleLocalization.lean`.  All headline declarations use
only `[propext]`; there are no residual hypotheses hidden as axioms.
