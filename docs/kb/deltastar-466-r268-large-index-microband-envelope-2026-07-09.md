# #466 R268: large-index micro-band envelope

Date: 2026-07-09

## Question

R267 makes the finite branch `M < 1536` small. R268 asks how soft the
large-index theorem can be for `M >= 1536`.

Command:

```bash
python3 scripts/probes/probe_r268_large_index_microband_envelope.py --max-index 8000
```

## Result

Worst large-index rows:

```text
S        n     p          M
0.405233 1024  1604609    1567
0.403073 512   1299457    2538
0.402592 512   1264129    2469
0.402116 512   1161217    2268
0.401899 512   2912257    5688
```

Constant cap scan:

```text
cap=0.4060 violations=0
cap=0.4055 violations=0
cap=0.4050 violations=1
cap=0.4040 violations=1
cap=0.4030 violations=2
```

Thus the large branch can target the much softer theorem

```text
M >= 1536 => S(0.75) <= 0.4055.
```

This has margin relative to the global cap `612/1485 ~= 0.412121`.

## Route update

The direct micro-band theorem can be split as:

1. finite branch `512 <= M < 1536`, 465 rows total;
2. large branch `M >= 1536`, prove `S(0.75) <= 0.4055`.

The large branch is no longer knife-edge and may admit a softer analytic
vertical-distribution proof.

## Stratified high-index sample

The full sweep beyond `M=8000` is expensive, so R268 also supports stride and
per-level limits. Command:

```bash
python3 scripts/probes/probe_r268_large_index_microband_envelope.py \
  --min-index 8001 --max-index 20000 --stride 17 --limit-per-n 80 \
  --chunk 8192 --top 20
```

Output:

```text
cases=240
worst S=0.396309 at n=1024, p=9376769, M=9157
```

All sampled high-index rows are far below the proposed `0.4055` cap. This
supports the view that the large-branch maximum is near the lower edge
`M ~= 1536`, not drifting upward at larger `M`.
