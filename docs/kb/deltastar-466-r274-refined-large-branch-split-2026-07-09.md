# #466 R274: refined large-branch split

Date: 2026-07-09

## Question

R273 localizes the large-branch worst row at `M=1567`. R274 checks whether
splitting again at `M=2048` gives an even softer high-index theorem.

Commands:

```bash
python3 scripts/probes/probe_r268_large_index_microband_envelope.py \
  --min-index 2048 --max-index 8000 --chunk 8192 --top 12

python3 scripts/probes/probe_r273_large_index_quantile_cap.py \
  --min-index 2048 --max-index 8000 --chunk 8192 --top 12
```

## Result

For `M >= 2048`, worst survival:

```text
S=0.403073 at n=512, p=1299457, M=2538
```

Constant cap scan:

```text
cap=0.4050 violations=0
cap=0.4040 violations=0
cap=0.4030 violations=1
```

Worst q60 for `M >= 2048`:

```text
q60=0.75889031 at n=1024, p=3474433, M=3393
```

## Route update

The micro-band split can be refined:

```text
finite branch A:
  512 <= M < 1536
  CSV certificate from R269/R270.

finite/edge branch B:
  1536 <= M < 2048
  small finite edge around the previous large-branch worst M=1567.

high-index branch:
  M >= 2048
  prove S(0.75) <= 0.404
  or prove q60 <= 0.759.
```

This removes the `M=1567` edge row from the analytic large branch and gives
another `~0.0015` survival slack beyond the already-soft `0.4055` cap.
