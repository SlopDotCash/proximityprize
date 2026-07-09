# #466 R278: high-index finite certificate

Date: 2026-07-09

## Purpose

R276 left an analytic branch beginning at `M >= 2048`.  R277 showed that the
range `2048 <= M <= 8000` is still where the observed q60 frontier lives.  R278
turns that whole midrange into a finite CSV certificate, leaving only a cleaner
asymptotic branch.

## Artifact

CSV:

```text
docs/kb/data/deltastar-466-r278-high-index-finite-microband-certificate.csv
```

Generation command:

```text
python3 scripts/probes/probe_r269_finite_microband_certificate_csv.py \
  --min-index 2048 \
  --max-index-exclusive 8001 \
  --cache-only \
  --out docs/kb/data/deltastar-466-r278-high-index-finite-microband-certificate.csv
```

Output:

```text
R269 finite micro-band CSV rows=2476 skipped=0
best n=512 p=1299457 M=2538 count=1023
micro=0.587936175336 slack=0.013263824664
```

Independent verifier:

```text
python3 scripts/probes/probe_r270_verify_finite_microband_certificate.py \
  --csv docs/kb/data/deltastar-466-r278-high-index-finite-microband-certificate.csv
```

Output:

```text
R270 verify finite micro-band CSV rows=2476 failures=0
worst micro=0.587936175336 slack=0.013263824664
n=512 p=1299457 M=2538 count=1023
```

## Updated branch map

The trim-five micro-band branch can now be organized as:

```text
512 <= M < 1536:
  R269/R270 finite certificate

1536 <= M < 2048:
  R275/R270 finite certificate

2048 <= M <= 8000:
  R278/R270 finite certificate

M >= 8001:
  remaining analytic branch
```

The remaining analytic target is now:

```text
M >= 8001 => S(0.75) <= 0.404
```

Observed stratified evidence is substantially stronger:

```text
sampled M in [8001,20000]:
  worst S(0.75)=0.39630883
  worst q60=0.74089036
```

This suggests the final theorem should be an asymptotic large-index statement,
not a delicate finite edge estimate.
