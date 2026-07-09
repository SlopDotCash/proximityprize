# R258 trimmed fine-layer socket

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R257 found that the fine layer

```text
R = X_64 - lift(X_32)
```

has small aggregate rank mass but a few huge isolated positive spikes.  R258
asks whether deleting the top fine residual spike makes the remaining fine
layer tail theorem-shaped.

## Command

```bash
python3 -m py_compile scripts/probes/probe_r257_n64_fine_layer_tail.py
for trim in 0 1 2 4 8; do
  python3 scripts/probes/probe_r257_n64_fine_layer_tail.py \
    --min-index 512 --max-index 12000 --chunk 8192 \
    --tau 0.5 --trim "$trim" --sort c_tail --top 5
done
```

## Result

The untrimmed fine layer is dominated by single-spike events:

```text
trim=0:
  max C_tail = 2.35461364
  witness M=10404 p=665857 theta=20.2126 count=1
```

Deleting just the largest fine residual spike collapses the tail constant:

```text
trim=1:
  max C_tail = 0.38191713
  witness M=1024 p=65537 theta=8.046 count=7
```

Additional trimming gives only marginal improvement:

```text
trim=2: max C_tail = 0.36851375
trim=4: max C_tail = 0.36393594
trim=8: max C_tail = 0.35478031
```

The top fine-rank mass is small throughout the window:

```text
max fine_top8  = 0.08351014
max fine_top16 = 0.11506403
max fine_mgf   = 1.11435693
```

## Route update

This is the cleanest positive signal after the rank-sum refutations:

```text
X_64 = lift(X_32) + R_fine

pay one fine residual spike directly;
prove, after deleting that spike,
  S_fine(theta) <= 0.382 * exp(-theta/2) for theta > 0.5.
```

Unlike whole-spectrum rank-sum control, this isolates the high resonance into a
single fine-layer spike and leaves a much cheaper residual tail.  The remaining
proof challenge is to combine this additive fine-layer decomposition with an
MGF inequality that does not overpay `exp((X_32 + R_fine)/4)` by a crude product
bound.
