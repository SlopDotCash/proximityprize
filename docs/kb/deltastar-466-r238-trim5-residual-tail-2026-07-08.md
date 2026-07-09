# R238 trim-five residual tail

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Question

After R231/R237 split the certificate into a top-five contribution plus a
residual tail, R238 isolates the residual tail:

```text
after deleting top five values,
#{residual X >= theta} <= C * M * exp(-theta/2), theta > tau.
```

## Probe

New script:

```text
scripts/probes/probe_r238_trim5_residual_tail.py
```

It computes the exact required `C` on cached/exact quotient spectra after
deleting the top `trim` values.

## Cached main-lane result

Command:

```bash
python3 -m py_compile scripts/probes/probe_r238_trim5_residual_tail.py
python3 scripts/probes/probe_r238_trim5_residual_tail.py \
  --cache-only --top 12 --taus 0.5 0.625 0.75 0.875 1.0
```

On the cached `n >= 256`, `M <= 4096` subset:

```text
tau=0.5   worst_C=0.66397290  fails target C=0.6012
tau=0.625 worst_C=0.64383375  fails target C=0.6012
tau=0.75  worst_C=0.60110935  barely passes
tau=0.875 worst_C=0.58493329  passes with slack
tau=1.0   worst_C=0.56009182  passes with slack
```

The live residual-tail target is therefore:

```text
trim = 5
tau = 0.75
C = 0.6012
K = 0
```

Worst row at `tau=0.75`:

```text
n=512
p=417793
M=816
theta=0.756650
residual count=336
C_req=0.60110935
```

## Full small-n sweep and finite resonances

Follow-up command:

```bash
python3 scripts/probes/probe_r238_trim5_residual_tail.py \
  --medium-min-a 3 --medium-max-a 10 --medium-max-index 4096 \
  --min-index 512 --chunk 8192 --trim 5 \
  --taus 0.5 0.625 0.75 0.875 1.0 --target-c 0.650 --top 12
```

When `a < 8` is included, the residual tail is refuted by the same finite
resonance rows already isolated in the direct-MGF census:

```text
tau=0.75 worst_C=1.46437295
n=64 p=204353 M=3193 theta=14.127698 residual count=4
```

Other failing rows include `(128,231169,1806)`, `(64,65537,1024)`,
`(32,65537,2048)`, `(64,259201,4050)`, and `(64,249217,3894)`.  Thus the
trim-five tail is not a uniform all-`n` theorem; it needs the finite-exception
branch from R234/R235.

The asymptotic branch remains intact under the wider `n >= 256`, `M <= 5000`
sweep:

```bash
python3 scripts/probes/probe_r238_trim5_residual_tail.py \
  --medium-min-a 8 --medium-max-a 12 --medium-max-index 5000 \
  --min-index 512 --chunk 8192 --trim 5 \
  --taus 0.5 0.625 0.75 0.875 1.0 --target-c 0.650 --top 12
```

Result:

```text
cases=3098
tau=0.5   worst_C=0.66397290
tau=0.625 worst_C=0.64383375
tau=0.75  worst_C=0.60110935
tau=0.875 worst_C=0.58493329
tau=1.0   worst_C=0.56636847
```

## Why not raise tau?

Raising `tau` gives a better residual tail constant, but the low-band payment
in the MGF budget becomes too expensive.  Rechecking the full R231 budget:

```bash
python3 scripts/probes/probe_r231_top_spike_trimmed_mgf.py \
  --medium-min-a 8 --medium-max-a 10 --medium-max-index 4096 \
  --min-index 512 --chunk 8192 --cache-dir .cache/proximity-r231 \
  --cache-only --top 16 --trims 5 --taus 0.75 0.875 1.0 \
  --spike-budgets 0 --step 0.03125 --cutoff 0
```

gives:

```text
tau=0.75  total=1.995028  feasible
tau=0.875 total=2.0054    infeasible
tau=1.0   total=2.0115    infeasible
```

Thus `tau=0.75` is not arbitrary; it is the narrow optimum balancing residual
tail strength against low-band overpayment.

## Interpretation

The current main-lane theorem target is:

```text
Top five:
  top-five payment, with the R237 constant 4.5 now refuted
  on the wider sweep.

Residual:
  after deleting the top five quotient orbits,
  N_res(theta) <= 0.6012 * M * exp(-theta/2)
  for theta > 0.75.
```

Together with finite exceptions from R235, the residual half remains viable.
The top-five half must be repaired before this can replace the top-eight
rank-sum route.
