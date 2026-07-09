# δ* #466 — R200 vectorized large-grid sweep

R199 removed the immediate scalar-loop bottleneck by evaluating exact dyadic
Gauss-period cosets in NumPy chunks.  R200 turns that into a wider large-index
stress harness for the live R189/R197 branch:

```text
N(T) <= (3/5) M exp(-T/2) + 2,       M = (p - 1)/n >= 32.
```

The new probe is:

```text
scripts/probes/probe_r200_vectorized_large_grid_sweep.py
```

It generates congruence-prime rows for dyadic `n`, with starts near `n^2`,
`n^3`, `n^4`, `2n^4`, and `n^5` where applicable, then reuses the exact
R199 vectorized period evaluator.  For each row it reports:

- worst positive tail excess for the bulk-plus-two law;
- direct `MGF(1/4)`;
- normalized max/spike ratio `exp(max X / 4) / M`.

## Smoke run

```text
python3 scripts/probes/probe_r200_vectorized_large_grid_sweep.py \
  --max-n 128 --max-p 30000000 --primes-per-start 1 --chunk 32768
```

Result:

```text
tested=13 violations=0 max_positive_excess=0.000000
worst_spike_ratio=0.131736 n=32 p=1153 M=36
worst_mgf=1.411821 n=128 p=17921 M=140
```

## Broader run

```text
python3 scripts/probes/probe_r200_vectorized_large_grid_sweep.py \
  --max-n 512 --max-p 350000000 --primes-per-start 1 --chunk 32768
```

Result:

```text
tested=23 violations=0 max_positive_excess=0.000000
worst_spike_ratio=0.131736 n=32 p=1153 M=36
worst_mgf=1.467002 n=512 p=262657 M=513
```

The intended reading is brutally simple: any positive excess falsifies the
current large-branch hypothesis and should redirect the proof route; no
positive excess means the R189/R193/R197 pathway remains a live target, with
the worst row identifying the next analytic obstruction.

## Proof relevance

R200 is still evidence, not a theorem.  Its purpose is to locate the sharp
large-index failure mode before we invest in a formal analytic statement.  The
current Lean consumers already reduce the quarter-MGF route to:

1. finite direct `M < 32` certificates;
2. a large-index bulk tail bound;
3. a logarithmic max/spike-mass bound.

R200 attacks (2) and records diagnostics for (3).
