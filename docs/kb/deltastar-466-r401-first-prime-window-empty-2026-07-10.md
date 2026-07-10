# R401: the first prize-shaped low-rate Johnson windows are empty (2026-07-10)

Status: unconditional, axiom-clean operational result at the certified `2^30` production scale.

## Certified instance

Let

```text
n = 2^30,
epsilon* = 2^-128,
P = 2^30 * (2^128 + 192) + 1.
```

`Frontier/_PrizeShapePrimeP30.lean` proves that `P` is prime and gives an explicit element of
exact order `2^30` in `F_P`.  Hence this is a literal smooth-domain prime-field instance with the
advertised length and security scale.  Moreover

```text
floor(P / 2^128) = 2^30 = n.
```

## Threshold ceilings

The overlap-packing witness proves the faithful operational ceilings

```text
delta*(rate 1/4)  <= 1/2,
delta*(rate 1/8)  <= 1/2,
delta*(rate 1/16) <= 1/2.
```

These are faithful `mcaDeltaStar` bounds, not far-line surrogates or conditional named Props.
`Frontier/_PrizeShapeFirstPrimeBelowJohnson.lean` records their Johnson comparison:

```text
1/2 < 1 - sqrt(1/8),
1/2 < 1 - sqrt(1/16) = 3/4.
```

Therefore the operational thresholds at rates `1/8` and `1/16` are strictly below Johnson.

At rate `1/4`, `1/2` is exactly Johnson.  The ceiling excludes every radius strictly above
Johnson, which is the advertised open window; it does not decide goodness at the Johnson endpoint
or claim an exact threshold.

## Empty advertised windows

The file proves the stronger budget statement.  For every valid radius `delta`:

```text
delta >= 1-sqrt(1/8)
  => not (epsMCA(RS[P,n,n/8],delta) <= 2^-128),

delta >= 1-sqrt(1/16)
  => not (epsMCA(RS[P,n,n/16],delta) <= 2^-128).
```

Thus the entire advertised above-Johnson MCA window is empty for these two certified instances.
This follows from the strict threshold ceilings and the operational ledger's rule that any good
valid radius is at most `mcaDeltaStar`.

The same file proves the rate-`1/4` open-window statement:

```text
delta > 1-sqrt(1/4) = 1/2
  => not (epsMCA(RS[P,n,n/4],delta) <= 2^-128).
```

Consequently one certified production-shaped field has empty above-Johnson operational windows at
all three lower advertised rates `1/4`, `1/8`, and `1/16`.

## Prize interpretation

`Frontier/_PrizeShapeGrandChallengeRefutation.lean` additionally checks the attainment issue in
the repository's official real-valued statement.  At rate `1/16`, every radius strictly below
`1/2` is good, `1/2` is bad, and the supremum is exactly `1/2`.  Hence the good-radius set has
no largest element, whereas `GrandMCAResolution` requires a good attained maximum.  Lean proves

```text
not_grandMCAChallengeRS_rateSixteenth
not_mcaPrize_firstPrimeDomain
```

The last theorem uses the official `prizeRates` index and machine-checks that its floored
rate-`1/16` dimension is `2^26`.  This is a formal refutation of the current real-valued `mcaPrize`
predicate on the certified smooth domain.  It is not a refutation of the faithful lattice
challenge: there the maximal good point is the predecessor rung, exactly as intended.

This is a decisive correction to any universal claim that every advertised low-rate production
instance has its operational threshold inside the above-Johnson window.  It does not prove or
refute the ignored-source polynomial `mcaConjecture`, whose right-hand side is not fixed to the
security budget.  It also leaves the rate-`1/2`, the exact rate-`1/4` threshold and Johnson
endpoint, and larger-budget threshold curves open.

The Lean axiom audit contains no `sorryAx`; only the standard logical quotient axioms occur.
