# #466 R283: second shoulder certificate

Date: 2026-07-09

## Purpose

After R282, the remaining branch was:

```text
M >= 10001 => S(0.75) <= 0.404
```

Cache-only evidence on `10001 <= M <= 20000` showed a second shoulder around
`M = 11k..14k`, with max cached `S(0.75) = 0.395190`.  R283 certifies the
front of that shoulder exactly.

## Artifact

CSV:

```text
docs/kb/data/deltastar-466-r283-second-shoulder-microband-certificate.csv
```

Generation and verification:

```text
python3 scripts/probes/probe_r269_finite_microband_certificate_csv.py \
  --min-index 10001 \
  --max-index-exclusive 15000 \
  --out docs/kb/data/deltastar-466-r283-second-shoulder-microband-certificate.csv

python3 scripts/probes/probe_r270_verify_finite_microband_certificate.py \
  --csv docs/kb/data/deltastar-466-r283-second-shoulder-microband-certificate.csv
```

Verifier output:

```text
R270 verify finite micro-band CSV rows=1903 failures=0
worst micro=0.577397213926 slack=0.023802786074
n=1024 p=11591681 M=11320 count=4481
```

## Tail evidence after the certificate

Cache-only scan:

```text
python3 scripts/probes/probe_r268_large_index_microband_envelope.py \
  --min-index 15000 \
  --max-index 50000 \
  --cache-only \
  --top 20
```

Output summary:

```text
cases=836 skipped=11837
max cached S(0.75)=0.393734 at n=256 p=4347137 M=16981
```

## Updated final branch

Finite coverage now extends through `M=14999`:

```text
512 <= M < 1536       R269/R270
1536 <= M < 2048      R275/R270
2048 <= M <= 8000     R278/R270
8001 <= M < 8192      R281/R270
8192 <= M <= 10000    R282/R270
10001 <= M < 15000    R283/R270
```

The remaining required theorem is:

```text
M >= 15000 => S(0.75) <= 0.404
```

The stronger working target, consistent with current cached evidence, is:

```text
M >= 15000 => S(0.75) <= 0.397
```

The exact frontier has moved downward from `0.403073` at `M=2538`, to
`0.396309` at `M=9157`, to `0.39511` in the second shoulder, and the cached
tail beyond `15000` is below `0.394`.
