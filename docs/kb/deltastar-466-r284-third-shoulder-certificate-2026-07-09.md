# #466 R284: third shoulder certificate

Date: 2026-07-09

## Purpose

R283 moved finite micro-band coverage through `M=14999`.  R284 certifies the
next block:

```text
15000 <= M < 20000
```

## Artifact

CSV:

```text
docs/kb/data/deltastar-466-r284-third-shoulder-microband-certificate.csv
```

Generation and verification:

```text
python3 scripts/probes/probe_r269_finite_microband_certificate_csv.py \
  --min-index 15000 \
  --max-index-exclusive 20000 \
  --out docs/kb/data/deltastar-466-r284-third-shoulder-microband-certificate.csv

python3 scripts/probes/probe_r270_verify_finite_microband_certificate.py \
  --csv docs/kb/data/deltastar-466-r284-third-shoulder-microband-certificate.csv
```

Verifier output:

```text
R270 verify finite micro-band CSV rows=1886 failures=0
worst micro=0.574744836203 slack=0.026455163797
n=512 p=7906817 M=15443 count=6085
```

## Tail evidence after the certificate

Cache-only scan:

```text
python3 scripts/probes/probe_r268_large_index_microband_envelope.py \
  --min-index 20000 \
  --max-index 100000 \
  --cache-only \
  --top 20
```

Output summary:

```text
cases=232 skipped=27830
max cached S(0.75)=0.39019695 at n=1024 p=34575361 M=33765
max cached q60=0.72248056 at the same case
```

## Updated final branch

Finite coverage now extends through `M=19999`:

```text
512 <= M < 1536       R269/R270
1536 <= M < 2048      R275/R270
2048 <= M <= 8000     R278/R270
8001 <= M < 8192      R281/R270
8192 <= M <= 10000    R282/R270
10001 <= M < 15000    R283/R270
15000 <= M < 20000    R284/R270
```

The remaining required theorem is:

```text
M >= 20000 => S(0.75) <= 0.404
```

The stronger working target, consistent with current cached evidence, is:

```text
M >= 20000 => S(0.75) <= 0.392
```

The cached q60 target is correspondingly much stronger than before:

```text
M >= 20000 => q60 <= 0.723
```
