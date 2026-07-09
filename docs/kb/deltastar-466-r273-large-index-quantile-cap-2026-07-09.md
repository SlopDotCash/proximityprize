# #466 R273: large-index quantile cap

Date: 2026-07-09

## Question

R272 refutes ordinary moment bounds for the large branch. R273 checks whether
the soft cap `S(0.75) <= 0.4055` is better phrased as a quantile cap.

Command:

```bash
python3 scripts/probes/probe_r273_large_index_quantile_cap.py --max-index 8000
```

## Result

Worst large-index row:

```text
S        q55      q575     q60      q625     q65      n     p          M
0.405233 0.632978 0.707806 0.767826 0.846473 0.923355 1024  1604609    1567
```

Quantile maxima:

```text
q55  max=0.63297834 at same worst-S row
q575 max=0.70780572 at same worst-S row
q60  max=0.76782568 at same worst-S row
q625 max=0.85535641 at n=256, M=1966
q65  max=0.93217365 at n=512, M=1551
```

Correlations with `S(0.75)`:

```text
q55      +0.775398
q575     +0.852039
q60      +0.943292
q625     +0.954793
q65      +0.848627
```

## Route update

The large branch is again a lower-bulk quantile problem, not a moment problem.
A clean sufficient target is:

```text
M >= 1536 => q60 <= 0.768
```

or a slightly higher-quantile formulation around `q625 <= 0.856`. The q60 cap
has the advantage that the same row controls both `S(0.75)` and `q60`.

## Stratified high-index sample

Command:

```bash
python3 scripts/probes/probe_r273_large_index_quantile_cap.py \
  --min-index 8001 --max-index 20000 --stride 17 --limit-per-n 80 \
  --chunk 8192 --top 20
```

Output:

```text
cases=240
max q60=0.74089036 at n=1024, p=9376769, M=9157
max S=0.39630883 at the same row
```

The high-index q60 envelope is far below the proposed `q60 <= 0.768` target.
This suggests the large-branch difficulty is localized near the lower edge
`M ~= 1536`.
