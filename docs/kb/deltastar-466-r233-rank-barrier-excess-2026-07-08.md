# R233: rank-barrier excess scan

Issue: #466. Date: 2026-07-08.

## Question

R232 split the quotient-MGF obstruction into a narrow top-spike resonance and
a broader multi-spike/bulk regime.  R233 tests whether sorted quotient order
statistics give a cleaner direct route than all-threshold survival envelopes.

For quotient normalized squares `X_q`, write `X_(r)` for the descending order
statistics.  The tested barrier is:

```text
X_(r) <= 4 log(B * M / r^alpha)
```

Equivalently:

```text
exp(X_(r)/4) <= B * M / r^alpha.
```

If `alpha > 1` held uniformly with a small enough `B`, this would give a
summable direct quarter-MGF route.

## Probe

New script:

```text
scripts/probes/probe_r233_rank_barrier_excess.py
```

Compile check:

```text
python3 -m py_compile scripts/probes/probe_r233_rank_barrier_excess.py
```

Medium exact sweep:

```text
python3 scripts/probes/probe_r233_rank_barrier_excess.py \
  --medium-max-a 8 --medium-max-index 2048 --min-index 512 \
  --chunk 8192 --top 24
```

Result for the harmonic rank barrier `alpha=1, B=1`:

```text
cases=1684
worst_all=2.050213 n=64 p=65537 rank=1
next rows already have negative excess:
  n=128 p=65537 excess=-0.467 rank=1
  n=64  p=48449 excess=-1.525 rank=1
```

Larger exact sweep with a small relaxation:

```text
python3 scripts/probes/probe_r233_rank_barrier_excess.py \
  --medium-max-a 9 --medium-max-index 4096 --min-index 512 \
  --chunk 8192 --b-factor 1.75 --top 20
```

Summary:

```text
cases=4266
worst_all=-0.188250 n=64 p=65537 rank=1
```

With `B=2`, the margin is wider:

```text
cases=4266
worst_all=-0.722375 n=64 p=65537 rank=1
```

So the harmonic rank barrier with a small constant isolates the top-spike
issue extremely well.  However, harmonic decay is not summable.

## Summable power test

The summable variants fail for a different reason: the middle bulk ranks are
too large, even when the total quarter-MGF is harmless.

For `alpha=1.5, B=1`:

```text
cases=4266
worst_all=8.859614 n=512 p=262657 rank=256 mgf1/4=1.467002
```

For `alpha=2, B=1`:

```text
cases=4266
worst_all=19.949969 n=512 p=262657 rank=256 mgf1/4=1.467002
```

The failure is not a dangerous top spike; it is ordinary bulk mass around
rank 256.

## Interpretation

The sorted-rank view is useful but does not close the prize:

- A harmonic rank barrier with `B < 2` appears to cover the tested quotient
  spectra after the single sharp `n=64, p=65537` top-spike row is absorbed.
- A summable power-rank law is false in the middle bulk, so it should not be
  encoded as a Lean residual.
- The next plausible direct-MGF shape must be two-component:
  top ranks controlled by a harmonic/rank-barrier theorem, and bulk ranks
  controlled by a separate distributional or variance law.

This gives a cleaner successor to the failed R230/R231 survival envelopes:
do not try to make one tail inequality pay for both top spikes and bulk.
Use a rank-local top-spike theorem plus an independent bulk-MGF theorem.

No prize closure is claimed.
