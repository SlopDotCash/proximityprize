# δ* #466 — multi-prime stress for dyadic child angles (2026-07-08)

## Hypothesis

R183 found that child-pair angles in the dyadic tower are nearly uniform at
one representative prime per row.  R184 checks whether this is a representative
phenomenon or whether nearby same-regime primes can produce a visible low
harmonic.

Probe: `scripts/probes/probe_r184_multi_prime_angle_stress.py`.

## Result

Default fast stress:

```text
n 16 -> 32
1048609 pairs 32769 disc16 0.00345 maxF 0.00966 f4 0.00539
1048897 pairs 32778 disc16 0.00304 maxF 0.00928 f4 0.00875
1049057 pairs 32783 disc16 0.00216 maxF 0.00875 f4 0.00875
1049089 pairs 32784 disc16 0.00256 maxF 0.00653 f4 0.00636
1049281 pairs 32790 disc16 0.00334 maxF 0.01059 f4 0.00499
n 32 -> 64
16777601 pairs 262150 disc16 0.00080 maxF 0.00380 f4 0.00380
16777729 pairs 262152 disc16 0.00095 maxF 0.00424 f4 0.00350
16778497 pairs 262164 disc16 0.00117 maxF 0.00319 f4 0.00319
16778561 pairs 262165 disc16 0.00100 maxF 0.00414 f4 0.00414
16778689 pairs 262167 disc16 0.00102 maxF 0.00566 f4 0.00566
```

A partial heavier run also reached the first three `64 -> 128` primes before
manual stop:

```text
268437889 pairs 2097171 disc16 0.00035 maxF 0.00226 f4 0.00226
268438657 pairs 2097177 disc16 0.00040 maxF 0.00172 f4 0.00172
268438913 pairs 2097179 disc16 0.00046 maxF 0.00174 f4 0.00174
```

## Verdict

The child-angle equidistribution phenomenon is stable across nearby primes.
No low harmonic among `1..8` spikes in the tested same-regime cells.

The proof target remains:

```text
Bound finitely many Fourier coefficients of the child-angle measure strongly
enough to preserve the R168 bin-budget/MGF invariant.
```

This is now a falsifiable, finite-harmonic form of the dyadic tower route.
