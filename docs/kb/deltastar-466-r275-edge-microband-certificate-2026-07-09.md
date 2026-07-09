# #466 R275: edge micro-band certificate

Date: 2026-07-09

## Purpose

R274 refines the micro-band split by carving out the edge branch
`1536 <= M < 2048`. R275 generates and verifies a CSV certificate for that
branch.

Generate:

```bash
python3 scripts/probes/probe_r269_finite_microband_certificate_csv.py \
  --min-index 1536 --max-index-exclusive 2048 \
  --out docs/kb/data/deltastar-466-r275-edge-microband-certificate.csv
```

Verify:

```bash
python3 scripts/probes/probe_r270_verify_finite_microband_certificate.py \
  --csv docs/kb/data/deltastar-466-r275-edge-microband-certificate.csv
```

Output:

```text
rows=217
failures=0
worst micro=0.591086303005
slack=0.010113696995
n=1024 p=1604609 M=1567 count=635
```

Top rows:

```text
1024,1604609,1567,5,0.75,635,0.405232929164,0.591086303005,0.010113696995
256,503297,1966,5,0.75,790,0.401831129196,0.586124323803,0.015075676197
256,438017,1711,5,0.75,685,0.400350672122,0.583964879602,0.017235120398
```

## Route update

The micro-band split now has two finite certificate tables:

```text
512 <= M < 1536: 465 rows, worst slack 0.000066
1536 <= M < 2048: 217 rows, worst slack 0.010114
```

The analytic branch can start at `M >= 2048`, where R274 supports the softer
target:

```text
S(0.75) <= 0.404
```

or the quantile target:

```text
q60 <= 0.759.
```
