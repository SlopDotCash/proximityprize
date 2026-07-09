# R230 low-band parameterized feasibility

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Question

After R228 refuted the all-threshold natural quotient envelope `(3/5, 2)`,
the next plausible repair was a low-band split:

```text
pay theta <= tau by the full carrier,
prove N_q(theta) <= Cbulk * M * exp(-theta/2) + Kquot only for tau < theta.
```

R230 drafts the Lean socket for this shape, but the analytic question is
whether any such simple exponential tail has enough weighted-budget slack to
prove the quarter-MGF target.

## Probe

New script:

```text
scripts/probes/probe_r230_low_band_param_feasibility.py
```

For exact quotient spectra it computes, for each `(tau, Kquot)`,

- the worst required `Cbulk`;
- the closed low-band staircase budget at that global `Cbulk`;
- whether the budget fits under the target `2`.

## Results

Moderate exact sweep:

```bash
python3 -m py_compile scripts/probes/probe_r230_low_band_param_feasibility.py
python3 scripts/probes/probe_r230_low_band_param_feasibility.py \
  --medium-max-a 9 --medium-max-index 512 --chunk 8192 --top 16 \
  --taus 0.5 0.75 1.0 1.25 1.5 2.0 --spike-budgets 2 3 4 6 --cutoff 0
```

Summary:

```text
cases=774
feasible_rows=0
best_budget=4.892449
slack=-2.892449
C_req=0.77255147
tau=0.5
K=2
```

Even after filtering to `M >= 128`:

```text
cases=558
feasible_rows=0
best_budget=3.776092
slack=-1.776092
C_req=0.77255147
tau=0.5
K=2
```

Larger exact sweep:

```bash
python3 scripts/probes/probe_r230_low_band_param_feasibility.py \
  --medium-max-a 8 --medium-max-index 4096 --min-index 512 --chunk 8192 \
  --top 20 --taus 0.5 1.0 1.5 2.0 4.0 8.0 \
  --spike-budgets 2 3 4 8 12 --cutoff 0
```

Summary:

```text
cases=3749
feasible_rows=0
best_budget=8.161802
slack=-6.161802
C_req=4.71284042
tau=2.0
K=2
```

Worst witness in the larger sweep:

```text
n=64
p=238081
M=3720
theta=19.543539
count=3
K=2
C_req=4.71284042
```

## Interpretation

The simple low-band exponential-tail-to-quarter-MGF route appears refuted.
The obstruction is not the low band; it is rare high-threshold multi-spike
behavior.  With `K=2`, three survivors near `theta ~= 19.54` at `M=3720`
force `Cbulk ~= 4.71`, which makes the weighted envelope far too expensive.
Increasing `K` reduces the required `Cbulk` but increases staircase spike mass;
none of the tested pairs fit the target budget.

This suggests the next analytic residual cannot be a one-parameter exponential
tail plus constant spike budget.  It needs a more structural treatment of the
top spikes: exact top-k removal, arithmetic classification of spike clusters,
or a non-survival route that bounds the MGF directly from orbit/variance
structure.

## Lean status

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R230ParamLowBandQuotientMGFEndpoint.lean`
was drafted as a parameterized socket, but was not verified in this run because
the local mathlib cache is missing oleans such as:

```text
Mathlib.Tactic.Positivity.Core.olean
Mathlib.Algebra.Group.Units.Hom.olean
```

The required cache repair/build was blocked by a long-held checkout lock, so
R230 should not be counted as landed until `pg-iterate` succeeds.
