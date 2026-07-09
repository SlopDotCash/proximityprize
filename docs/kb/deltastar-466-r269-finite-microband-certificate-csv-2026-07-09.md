# #466 R269: finite micro-band certificate CSV

Date: 2026-07-09

## Purpose

R267 shows the finite branch `512 <= M < 1536` has only 465 rows. R269 turns
that branch into a stable CSV certificate with exact survivor counts.

Command:

```bash
python3 scripts/probes/probe_r269_finite_microband_certificate_csv.py --cache-only
```

Output:

```text
rows=465
skipped=0
out=docs/kb/data/deltastar-466-r269-finite-microband-certificate.csv
best n=512 p=760321 M=1485 count=612 micro=0.601133782897 slack=0.000066217103
```

CSV columns:

```text
n,p,M,trim,theta,count,survival,micro_cost,slack
```

Top rows:

```text
512,760321,1485,5,0.75,612,0.412121212121,0.601133782897,0.000066217103
512,620033,1211,5,0.75,499,0.412056151941,0.601038883942,0.000161116058
512,417793,816,5,0.75,336,0.411764705882,0.600613770974,0.000586229026
```

## Route update

The finite branch is now a reproducible data artifact that can be consumed by a
future verifier:

```text
docs/kb/data/deltastar-466-r269-finite-microband-certificate.csv
```

This supports the R266 split:

1. finite branch `M < 1536` by direct table certificate;
2. large branch `M >= 1536` by soft analytic cap `S(0.75) <= 0.4055`.
