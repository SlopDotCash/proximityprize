# #466 R356 — universal six-web resultant exclusion misses prize scale

For a genuine six-term polynomial with six distinct roots of unity, Parseval
and AM-GM give the universal resultant ceiling

```text
|Res(Φ_n, f)| ≤ 12^(n/4).
```

At `n = 64`, this is

```text
12^16 = 184,884,258,895,036,416,
```

whereas the prize window begins at `n^4 = 16,777,216`. The ratio is about
`1.10·10^10`. Therefore the generic resultant-divisor argument cannot show
that a prize-window prime avoids all genuine six-webs. It remains useful for
explaining individual bad primes—for example R355 has resultant `8p`—but not
for the uniform existence step.

The missing improvement must exploit either template-specific archimedean
height far below the AM-GM ceiling, cancellation among many templates, or a
direct finite-field incidence estimate. This is a quantitative refutation of
the naive “enumerate all six resultants and use their size” closure.
