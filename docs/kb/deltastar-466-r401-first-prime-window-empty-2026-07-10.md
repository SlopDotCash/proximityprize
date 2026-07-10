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

## Exact thresholds

The previously assembled all-stack incidence theorems and overlap-packing witness prove

```text
delta*(rate 1/8)  = 1/2,
delta*(rate 1/16) = 1/2.
```

These are faithful `mcaDeltaStar` equalities, not far-line surrogates or conditional named Props.
`Frontier/_PrizeShapeFirstPrimeBelowJohnson.lean` now records their missing consequence:

```text
1/2 < 1 - sqrt(1/8),
1/2 < 1 - sqrt(1/16) = 3/4.
```

Therefore both exact operational thresholds are strictly below Johnson.

## Empty advertised windows

The file proves the stronger budget statement.  For every valid radius `delta`:

```text
delta >= 1-sqrt(1/8)
  => not (epsMCA(RS[P,n,n/8],delta) <= 2^-128),

delta >= 1-sqrt(1/16)
  => not (epsMCA(RS[P,n,n/16],delta) <= 2^-128).
```

Thus the entire advertised above-Johnson MCA window is empty for these two certified instances.
This follows rigorously from the exact threshold equalities and the operational ledger's rule that
any good radius is at most `mcaDeltaStar`.

## Field sensitivity

A second certified prize-shaped prime has the same length, rate `1/16`, and security target, but
its normalized scalar budget is `2n`.  The existing `17/32` theorem gives

```text
delta*(second prime, rate 1/16) >= 17/32 > 1/2
  = delta*(first prime, rate 1/16).
```

R401 packages this as an unconditional strict field-sensitivity theorem.  Consequently no formula
depending only on `(n,rho,epsilon*)` can describe the operational threshold across these fields;
the exact field size or normalized budget must be retained.

## Prize interpretation

This is a decisive correction to any universal claim that every advertised low-rate production
instance has its operational threshold inside the above-Johnson window.  It does not prove or
refute the ignored-source polynomial `mcaConjecture`, whose right-hand side is not fixed to the
security budget.  It also leaves the rate-`1/2`, saturated rate-`1/4`, and larger-budget threshold
curves open.

The Lean axiom audit contains no `sorryAx`; only the standard logical quotient axioms occur.
