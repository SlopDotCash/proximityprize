# δ* #466 — large-index bulk-plus-two tail stress (2026-07-08)

## Hypothesis

R197 split the quarter-MGF route into:

```text
M < 32:  finite direct certificates
M >= 32: R189/R190 bulk-plus-two tail route
```

R198 stress-tests the large branch:

```text
N(T) <= (3/5) M exp(-T/2) + 2.
```

## Probe

File: `scripts/probes/probe_r198_large_index_tail_stress.py`.

Fast exact run:

```text
python3 scripts/probes/probe_r198_large_index_tail_stress.py \
  --max-p 30000000 --max-n 512 --primes-per-start 3
```

The full default cap `--max-p 350000000` was intentionally interrupted after
several minutes because exact spectra for the largest multi-million-coset rows
are slow; the bounded run is the current reproducible stress verdict.

## Result

```text
tested = 53
violations = 0
max_positive_excess = 0
```

Worst rows:

```text
excess    mgf1/4  maxX    M        n     p
-0.194    1.5234  17.636  1031     32    32993
-0.356    1.4139  27.584  262164   64    16778497
-0.388    1.4363  6.843   38       32    1217
-1.103    1.4670  16.168  513      512   262657
```

## Verdict

The large-index branch remains alive.  Under the fast exact stress cap, the
R189 constants `(3/5, 2)` survive all expanded cases with room, including the
known R63 coherent-spike anchors.

Next pressure point: either optimize the exact implementation for the
multi-million-coset rows or prove the large-index bulk law analytically.
