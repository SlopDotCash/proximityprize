# #466 R281: dyadic bridge certificate

Date: 2026-07-09

## Purpose

R280 proposed moving the final analytic branch to the clean dyadic threshold:

```text
M >= 8192 => S(0.75) <= 0.394
```

That leaves a tiny bridge:

```text
8001 <= M < 8192
```

R281 certifies this bridge finitely.

## Artifact

CSV:

```text
docs/kb/data/deltastar-466-r281-dyadic-bridge-microband-certificate.csv
```

Generation command:

```text
python3 scripts/probes/probe_r269_finite_microband_certificate_csv.py \
  --min-index 8001 \
  --max-index-exclusive 8192 \
  --out docs/kb/data/deltastar-466-r281-dyadic-bridge-microband-certificate.csv
```

Output:

```text
R269 finite micro-band CSV rows=81 skipped=0
best n=1024 p=8380417 M=8184 count=3236
micro=0.576751933543 slack=0.024448066457
```

Independent verifier:

```text
python3 scripts/probes/probe_r270_verify_finite_microband_certificate.py \
  --csv docs/kb/data/deltastar-466-r281-dyadic-bridge-microband-certificate.csv
```

Output:

```text
R270 verify finite micro-band CSV rows=81 failures=0
worst micro=0.576751933543 slack=0.024448066457
n=1024 p=8380417 M=8184 count=3236
```

## Updated final branch

The finite coverage is now:

```text
512 <= M < 1536       R269/R270
1536 <= M < 2048      R275/R270
2048 <= M <= 8000     R278/R270
8001 <= M < 8192      R281/R270
```

The only remaining micro-band theorem is:

```text
M >= 8192 => S(0.75) <= 0.394
```

This implies the older required branch `S(0.75) <= 0.404` with substantial
constant slack.
