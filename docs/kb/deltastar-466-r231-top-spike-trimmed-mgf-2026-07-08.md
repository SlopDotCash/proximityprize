# R231 top-spike trimmed MGF feasibility

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Hypothesis

R230 refuted simple one-piece low-band exponential survival envelopes: rare
high-threshold multi-spike clusters force the bulk constant too high.  R231
tests the next shape:

```text
pay the top L quotient orbits exactly,
prove an exponential residual tail for the remaining quotient spectrum,
add the exact top-spike staircase contribution to the residual envelope budget.
```

This is aimed at replacing a crude constant spike budget by an arithmetic
classification/removal of the top few orbits.

## Probe

New script:

```text
scripts/probes/probe_r231_top_spike_trimmed_mgf.py
```

It computes, on exact quotient spectra:

- the global residual-tail constant `C_req` after trimming the top `L` values;
- the exact staircase contribution of the trimmed top values;
- the closed residual envelope budget;
- whether the total fits under the quarter-MGF target `2`.

## Results

Full medium set with `n` as low as `64` still fails because finite small rows
such as `n=64, p=65537` have too much exact MGF mass even after trimming:

```bash
python3 scripts/probes/probe_r231_top_spike_trimmed_mgf.py \
  --medium-max-a 8 --medium-max-index 2048 --min-index 512 --chunk 8192 \
  --top 24 --trims 2 4 8 16 32 --taus 0.5 1.0 2.0 \
  --spike-budgets 0 1 2 --cutoff 0
```

Summary:

```text
cases=1684
feasible_rows=0
best_budget=3.863974
trim=16
tau=0.5
K=0
```

Filtering to `n >= 256` changes the picture.  A coarse grid nearly fits:

```bash
python3 scripts/probes/probe_r231_top_spike_trimmed_mgf.py \
  --medium-min-a 8 --medium-max-a 10 --medium-max-index 2048 \
  --min-index 512 --chunk 8192 --top 24 \
  --trims 4 8 16 32 64 128 --taus 0.5 1.0 2.0 \
  --spike-budgets 0 1 2 --cutoff 0
```

Summary:

```text
cases=682
feasible_rows=0
best_budget=2.072940
trim=4
tau=0.5
K=0
```

Refining the staircase around the best region gives a positive certificate on
the tested window:

```bash
python3 scripts/probes/probe_r231_top_spike_trimmed_mgf.py \
  --medium-min-a 8 --medium-max-a 10 --medium-max-index 2048 \
  --min-index 512 --chunk 8192 --top 8 \
  --trims 4 --taus 0.75 --spike-budgets 0 \
  --step 0.03125 --cutoff 0
```

Output:

```text
cases=682
feasible_rows=1
best_budget=1.989608
slack=0.010392
C_req=0.60289836
trim=4
tau=0.75
K=0
```

The residual-tail witness is:

```text
n=512
p=417793
M=816
theta=0.756650
residual count=337
```

The worst total-budget row is:

```text
n=512
p=566273
M=1106
```

## Interpretation

This is the first positive signal after R228/R230:

```text
top 4 exact quotient orbits
+ residual tail above tau = 0.75
+ no residual additive spike budget
+ Cbulk about 0.603
=> quarter-MGF budget < 2 on the tested n >= 256, 512 <= M <= 2048 window.
```

The first broader `M <= 4096` run was interrupted during exact spectrum
generation, but it populated an on-disk cache with 1499 exact spectra.  Rerunning
on that cached subset refuted the top-4 version slightly:

```bash
python3 scripts/probes/probe_r231_top_spike_trimmed_mgf.py \
  --medium-min-a 8 --medium-max-a 10 --medium-max-index 4096 \
  --min-index 512 --chunk 8192 --cache-dir .cache/proximity-r231 \
  --cache-only --top 10 --trims 4 --taus 0.75 --spike-budgets 0 \
  --step 0.03125 --cutoff 0
```

Summary:

```text
cases=1499
feasible_rows=0
best_budget=2.003690
slack=-0.003690
C_req=0.62000046
trim=4
tau=0.75
K=0
```

The new obstruction is a fifth spike:

```text
n=256
p=771073
M=3012
theta=15.064649
residual count=1
```

Trimming five orbits repairs the cached broad subset:

```bash
python3 scripts/probes/probe_r231_top_spike_trimmed_mgf.py \
  --medium-min-a 8 --medium-max-a 10 --medium-max-index 4096 \
  --min-index 512 --chunk 8192 --cache-dir .cache/proximity-r231 \
  --cache-only --top 16 --trims 5 6 8 10 12 \
  --taus 0.625 0.75 0.875 1.0 --spike-budgets 0 \
  --step 0.03125 --cutoff 0
```

Summary:

```text
cases=1499
feasible_rows=2
best_budget=1.995028
slack=0.004972
C_req=0.60110935
trim=5
tau=0.75
K=0
```

The likely theorem shape is therefore not "bulk plus constant spikes"; it is
"classify/pay the top five quotient orbits and prove a half-rate residual tail
for the rest."  This fits the observed failure mode: top clusters break
survival envelopes, but paying them exactly leaves a near-half-rate residual
bulk.

Open stress item: complete the cached `M <= 4096` generation and rerun the
trim-5 candidate over the full set before promoting it to a formal residual.
