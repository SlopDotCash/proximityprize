# R230: spike-rank profile of MGF failures

Status: evidence for replacing flat spike budgets with rank-sensitive spike
control.

## Probe

Script:

```text
scripts/probes/probe_r230_spike_rank_profile.py
```

It sorts quotient normalized-square values `X_q` by descending MGF weight
`exp(X_q / 4)` and reports cumulative top-rank contribution to

```text
mean_q exp(X_q / 4).
```

It also reports the rank barrier excess

```text
X_(r) - 4 * log(M / r),
```

where `M = |Q|`.  The barrier is natural because one rank-`r` value with
`X_(r) = 4 log(M/r)` contributes about `1/r` to the average.

## Main output

Command:

```bash
python3 scripts/probes/probe_r230_spike_rank_profile.py \
  --ranks 1 2 4 8 16 32 64
```

Important rows:

```text
n=64 p=65537 M=1024
mgf=3.2624 top1=1.670 top64=2.148
topX=29.7761, 16.5884, 16.5249, 14.7440, ...
barrier_excess r1=+2.050, r2=-8.365

n=64 p=7937 M=124
mgf=2.7523 top1=1.422 top64=2.255
topX=20.6905, 8.5109, 7.0153, 5.5527, ...
barrier_excess r1=+1.409, r2=-7.998

n=64 p=204353 M=3193
mgf=2.6321 top1=0.962 top64=1.378
topX=32.1212, 23.8508, 18.1797, 15.4408, ...
barrier_excess r1=-0.154, r2=-5.651

n=64 p=421313 M=6583
mgf=1.6670 top1=0.104 top64=0.342
topX=26.0995, 22.3552, 21.5959, 19.9043, ...
barrier_excess r1=-9.069, r2=-10.041

n=64 p=16778497 M=262164
mgf=1.4139 top1=0.004 top64=0.019
topX=27.5838, 26.3525, 19.7138, 18.7236, ...
barrier_excess r1=-22.323
```

## Interpretation

The MGF failures are top-rank dominated, but not purely max-spike dominated.
For the Fermat row `n=64, p=65537`, the top orbit alone contributes `1.67`.
For `n=64, p=204353`, the top orbit contributes less than `1`, yet the
shoulder still pushes the MGF to `2.63`.

So a proof route based on only a maximum-spike bound is too coarse.  The next
useful analytic residual should control cumulative rank mass:

```text
sum_{j < R} exp(X_(j) / 4) / M
```

for moderate `R`, then use the one-band exponential quotient tail for the
remaining bulk.  This targets exactly what the flat `K/M` envelope loses: it
charges every top spike as if it persisted to the maximum threshold.

The large anchor rows have similar absolute maxima but enormous negative rank
barrier excess, so the same top spikes are harmless once divided by large
`M`.  This supports a hybrid strategy:

- finite/rank-sensitive certification for small and resonant medium `M`;
- rank barrier or ancestry bound for the top orbit cluster;
- R226 one-band quotient tail for the residual bulk.
