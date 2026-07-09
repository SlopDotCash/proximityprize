# #466 R354 — `RepThree` is false at the n=64 bad endpoint

At `p = 16,778,497`, let `ζ` generate `μ₆₄`. Exact modular arithmetic gives

```text
ζ^5 + ζ^6 + ζ^28 + ζ^29 − ζ^3 − ζ^25 = 0  (mod p).
```

Equivalently, the six subgroup elements

```text
ζ^5, ζ^6, ζ^28, ζ^29, −ζ^3, −ζ^25
```

sum to zero. Exhaustive checking of the 15 perfect matchings finds no pair
whose two entries are negatives. Hence this six-tuple is not antipodally
pairable and `RepThree (μ₆₄)` is false at this prize-scale bad prime.

The abstract obstruction is now machine-checked in
`_R353RepThreeCounterexample.lean`: any zero-sum six-tuple with no antipodal
pair refutes `RepThree`.

Consequently the order-six Gaussian consumer remains correct but cannot be
transferred uniformly to all prize primes. A successful wall proof must bound
the mass of these non-pairable six-webs (and their higher-rung descendants),
not assume their absence.
