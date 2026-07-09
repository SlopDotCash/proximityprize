# #466 R282: near-dyadic shoulder certificate

Date: 2026-07-09

## Refutation of the first R280 asymptotic guess

The R280 sampled grid suggested:

```text
M >= 8192 => S(0.75) <= 0.394
```

Exact enumeration of the near-dyadic shoulder refutes this.  The worst case in
`8192 <= M <= 10000` is:

```text
n=1024 p=9376769 M=9157 count=3629
S(0.75)=0.39630883
```

This is still safely below the required `0.404` cap, but above the speculative
`0.394` cap.

## Finite certificate

CSV:

```text
docs/kb/data/deltastar-466-r282-near-dyadic-shoulder-microband-certificate.csv
```

Generation and verification:

```text
python3 scripts/probes/probe_r269_finite_microband_certificate_csv.py \
  --min-index 8192 \
  --max-index-exclusive 10001 \
  --out docs/kb/data/deltastar-466-r282-near-dyadic-shoulder-microband-certificate.csv

python3 scripts/probes/probe_r270_verify_finite_microband_certificate.py \
  --csv docs/kb/data/deltastar-466-r282-near-dyadic-shoulder-microband-certificate.csv
```

Verifier output:

```text
R270 verify finite micro-band CSV rows=715 failures=0
worst micro=0.578069320468 slack=0.023130679532
n=1024 p=9376769 M=9157 count=3629
```

## Updated final branch

Finite coverage now extends through `M=10000`:

```text
512 <= M < 1536       R269/R270
1536 <= M < 2048      R275/R270
2048 <= M <= 8000     R278/R270
8001 <= M < 8192      R281/R270
8192 <= M <= 10000    R282/R270
```

The remaining micro-band theorem is now:

```text
M >= 10001 => S(0.75) <= 0.404
```

The stronger working target, consistent with current evidence, is:

```text
M >= 10001 => S(0.75) <= 0.397
```

The exact shoulder also gives a useful warning: sampled stride grids can miss
the frontier immediately after a dyadic boundary.
