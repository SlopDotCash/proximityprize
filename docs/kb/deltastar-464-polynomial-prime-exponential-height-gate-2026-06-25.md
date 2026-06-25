# Issue #464: polynomial prize primes versus exponential height gates

Date: 2026-06-25.

Status: **height-route obstruction**, not a delta-star proof.

## What Was Added

The file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PolynomialPrimeExponentialHeightGate.lean
```

formalizes a recurring quantitative failure mode in the Arakelov / resultant / cyclotomic-height
routes.

Many proposed good-prime certificates have this shape:

```text
height ceiling = B^d
good prime gate = B^d < p
```

where for dyadic cyclotomic fields

```text
d = phi(2^mu) = 2^(mu-1) = n/2.
```

The prize regime only promises a polynomial prime scale:

```text
p >= n^4.
```

The new Lean gate proves that if

```text
n^beta <= B^d,
```

then the promise `p >= n^beta` does **not** force `B^d < p`.  The witness is the boundary value
`p = n^beta`.

## Dyadic Failure

The concrete dyadic theorem is:

```text
for n = 2^mu, mu >= 6:
  n^4 <= 2^(n/2).
```

So the obstruction already appears at `n = 64`, even with the minimal nontrivial base `B = 2`:

```text
64^4 = 2^24 < 2^32 = 2^(64/2).
```

Consequently, any route whose only output is a generic archimedean height/norm ceiling

```text
B^(n/2)
```

cannot certify every prize-scale prime `p ~ n^4`.

## Critical Consequence

This does **not** refute the off-BGK bad-prime localization lane.  It separates two claims:

1. Generic height bound:

```text
all bad primes divide an integer of size at most B^(n/2)
```

This is too weak at prize scale.

2. Arithmetic smoothness/localization:

```text
the actual prime divisors of the relevant resultant are all < n^4
```

This remains the only useful height-style target.  It must exploit special structure of the
resultant family, not just product-over-conjugates height control.

## Verdict

Arakelov, Bilu, Mahler, and norm-product methods are prize-facing only if they produce **prime-divisor
localization** or **smoothness** beyond the generic `B^(n/2)` ceiling.  Product-height alone re-enters
the conjugate-count no-go and fails before the prize starts.
