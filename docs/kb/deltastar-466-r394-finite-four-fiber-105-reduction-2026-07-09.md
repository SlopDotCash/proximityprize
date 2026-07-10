# Issue #466 R394: finite-characteristic `105n` reduction

Date: 2026-07-09

R394 packages the exact finite-field component target:

```text
rep2(c) <= 4
primitive4(c) <= 9n
--------------------------------
rep4(c) <= (9 + 24*4)n = 105n.
```

The conclusion has exactly the same constant as R390's characteristic-zero theorem.

## Probe evidence

For `n=32, p=32993`, the primitive maximum is `272 = 8.5n`, close to the proposed `9n` boundary.
For every non-Sidon `n=64` prime in `[n^4,4n^4]`, pair multiplicity is exactly `4`; exact primitive
maxima are:

```text
p=17318209: 336 = 5.25n
p=19718977: 144 = 2.25n
p=26034433: 444 = 6.9375n
p=39451393: 144 = 2.25n
p=65456257: 360 = 5.625n
```

A generic comparison prime has primitive maximum `60 < n`. Thus the constants `4` and `9` survive
the known quartic exceptional spectrum and jointly recover the char-zero `105n` envelope. They are
still arithmetic conjectures, not claimed as proved by this consumer theorem.

At the next octave, an exhaustive sequential sample of 20,000 admissible primes near `n^4` for
`n=128` found seven non-Sidon primes and again every exceptional nonzero pair fiber had cardinality
exactly `4`; no fiber of cardinality `6` occurred. In unordered language, `PairMultiplicityFour`
is the assertion that no nonzero sum admits three distinct root pairs. Distinct pairs with the same
nonzero sum are automatically disjoint, so a counterexample is a six-root affine-involution
configuration. This is the precise arithmetic object to exclude.
