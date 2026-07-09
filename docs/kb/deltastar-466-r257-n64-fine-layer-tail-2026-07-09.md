# R257 n=64 fine-layer tail

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R256 showed that top `n=64` spikes retain large positive residuals after
subtracting the lifted `n=32` divisor spectrum.  R257 treats

```text
R = X_64 - lift(X_32)
```

as its own fine-layer spectrum and asks whether its rank/tail behavior is
cleaner than the full `X_64` spectrum.

## Probe

New script:

```text
scripts/probes/probe_r257_n64_fine_layer_tail.py
```

It reports fine-layer MGF, top-rank masses, maximum fine residual, and the
half-rate tail constant for `R`.

## Commands

```bash
python3 -m py_compile scripts/probes/probe_r257_n64_fine_layer_tail.py
python3 scripts/probes/probe_r257_n64_fine_layer_tail.py \
  --min-index 512 --max-index 12000 --chunk 8192 \
  --tau 0.5 --sort fine_top8 --top 25
python3 scripts/probes/probe_r257_n64_fine_layer_tail.py \
  --min-index 512 --max-index 12000 --chunk 8192 \
  --tau 0.5 --sort c_tail --top 25
```

## Findings

The fine layer has much smaller rank mass than the full spectrum:

```text
max fine_top8  = 0.08351014 at M=757, p=48449
max fine_top16 = 0.11506403 at M=757, p=48449
max fine_mgf   = 1.11435693 at M=1024, p=65537
```

This is far smaller than the full-spectrum top-rank masses that killed the
rank-sum route.

But the fine-layer single-spike tail is still large:

```text
max fine_max = 20.21264456 at M=10404, p=665857
max C_tail(tau=0.5) = 2.35461364 at M=10404, p=665857

M=10900, p=697601:
  fine_max=18.690
  C_tail=1.0494
```

Thus the fine layer is not uniformly sub-exponential under a plain half-rate
CDF.  It is, however, much more concentrated: the worst `C_tail` values are
single-spike events, while the aggregate fine rank mass is small.

## Route update

The next plausible socket is a two-level decomposition:

```text
X_64 = lift(X_32) + R_fine

pay the top one (or few) fine residual spikes directly;
prove a residual CDF for R_fine after deleting those spikes;
combine with a separate bound for the lifted X_32 layer.
```

This is more promising than whole-spectrum rank-sum control because the fine
top-rank budget is small, but it still requires classifying or paying isolated
fine residual spikes.
