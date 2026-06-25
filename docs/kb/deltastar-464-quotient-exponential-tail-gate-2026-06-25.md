# Issue #464: quotient exponential tail gate

Date: 2026-06-25.

Status: **rate consumer**, not a delta-star proof.

## What Was Added

The file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_QuotientExponentialTailGate.lean
```

packages the quotient tail consumer in exponential and subgaussian forms.

If a quotient score `Y : Q -> Real` satisfies

```text
quotientTailMass(Y, T) <= A * exp(-rate),
```

then the pulled-back pointwise bound

```text
Y(quot(a)) <= T
```

follows once

```text
#Q * A * exp(-rate) < 1.
```

The file also proves the logarithmic equivalent:

```text
log #Q + log A < rate.
```

For a subgaussian-looking tail, the named target is therefore:

```text
log #Q + log A < c * T^2 / V.
```

## Obstruction

The converse spike witness is also formalized.  If

```text
rate <= log #Q + log A,
```

then the exponential quotient-tail budget is still compatible with one bad quotient atom above
threshold.  In the subgaussian notation, the obstruction boundary is

```text
c * T^2 / V <= log #Q + log A.
```

At or below that boundary, a distributional tail estimate has not reached worst-case control.

## Prize-Relevant Reading

For the issue #464 quotient route, the intended quotient size is the dilation quotient

```text
#Q = m = (p - 1) / n.
```

At a proposed prize threshold

```text
T = C * sqrt(n * log m),
```

the analytic theorem must deliver enough rate that

```text
m * A * exp(-rate(T)) < 1.
```

Equivalently, it must prove

```text
log m + log A < rate(T).
```

Anything weaker remains compatible with the exact bad frequency the floor argument must exclude.
