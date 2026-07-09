# #466 R251: R249 split stress test

Date: 2026-07-09

## Question

R249 proposes a trim-five split certificate:

```text
micro = S(0.75) * exp(0.755/2)
tail  = sup_{theta >= 0.755} S(theta) * exp(theta/2)
```

with both quantities bounded by `0.6012`. R251 stress-tests this exact split
on cached spectra, including the `n=128` boundary.

## Main lane result

Command:

```bash
python3 scripts/probes/probe_r251_r249_split_stress.py \
  --cache-only --ns 256 512 1024 --max-index 4096 --top 12
```

Output:

```text
worst    slack    micro    tail     S_tau    tailTheta count  n     p          M
0.601134 0.000066 0.601134 0.598925 0.412121 0.757466  609    512   760321     1485
0.601109 0.000091 0.600614 0.601109 0.411765 0.756650  336    512   417793     816
0.601039 0.000161 0.601039 0.600681 0.412056 0.757821  498    512   620033     1211
```

The cached main lane `n >= 256` passes, but with tiny slack:

```text
worst=0.60113378
slack=0.00006622
```

## n=128 boundary

Command:

```bash
python3 scripts/probes/probe_r251_r249_split_stress.py \
  --cache-only --ns 128 --max-index 4096 --top 20
```

Output:

```text
worst    slack     micro    tail     S_tau    tailTheta count  n     p       M
1.089041 -0.487841 0.551632 1.089041 0.378184 13.782040 2      128   231169  1806
0.605025 -0.003825 0.601473 0.605025 0.412354 0.791216  244    128   76673   599
```

The first row is the known giant-spike exception from R234/R235. The second row
is a near-bulk `n=128` failure of the R249 split. It was hidden by the previous
top-five total-budget view because the `n=128` branch is already intended to
be finite-exception handled.

## Route update

The R249 split is stable for the cached main lane `n >= 256`, but **must not**
be claimed at `n=128`.

The honest theorem shape is:

```text
Main lane:
  n >= 256 => R249 split certificate.

Finite branch:
  handle n=128 exceptions directly, including at least
  (p,M) = (231169,1806) and (76673,599),
  plus the earlier R234/R235 direct-certificate exceptions.
```

This keeps the main analytic socket clean and avoids forcing a false uniform
statement across the small boundary level.

## Small uncached extension

Command:

```bash
python3 scripts/probes/probe_r251_r249_split_stress.py \
  --ns 256 512 --min-index 4097 --max-index 5000 --chunk 8192 --top 20
```

Output:

```text
cases=271
worst=0.57981159
slack=0.02138841
```

The extension beyond the cached `M <= 4096` window has comfortable slack. The
knife-edge rows are medium-index cases already present in the cache, not an
upward drift at larger quotient index.
