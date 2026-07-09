# R229: parameterized quotient envelope scan

Issue: #466. Date: 2026-07-08.

## Context

`_R229ParamQuotientEnvelopePrizeEndpoint.lean` exposes the quotient-to-prize
bookkeeping with arbitrary quotient constants `Cbulk` and `Kquot`.  The matching
probe `scripts/probes/probe_r229_one_band_mgf_cutoff_scan.py` tests the
one-band route

```text
N_q(theta) <= Cbulk * M * exp(-theta/2) + Kquot,  theta > tau,
```

and the resulting weighted staircase budget for the quarter-MGF target `<= 2`.

## Probe Results

Small/medium scan:

```text
python3 scripts/probes/probe_r229_one_band_mgf_cutoff_scan.py \
  --mode medium --medium-max-a 8 --medium-max-index 256 --top 20
```

Result summary:

```text
tested=361
env_failures=289
mgf_failures=1
worst_env=19.271132 at n=64, p=7937, M=124
worst_mgf=2.752305 at n=64, p=7937, M=124
min_passing_M=2
max_failing_M=256
```

Large-index slice:

```text
python3 scripts/probes/probe_r229_one_band_mgf_cutoff_scan.py \
  --mode medium --medium-max-a 10 --min-index 512 --medium-max-index 2048 --top 20
```

Result summary:

```text
tested=2130
env_failures=436
mgf_failures=4
worst_env=22.446739 at n=64, p=65537, M=1024
worst_mgf=3.262396 at n=64, p=65537, M=1024
min_passing_M=513
max_failing_M=2048
```

## Interpretation

The parameterized endpoint is the right bookkeeping surface, but the
`tau = 1`, `Cbulk = 3/5`, `Kquot = 12` one-band envelope is not a universal
MGF certificate.  Failures are driven by structured high-spike quotient
spectra, especially Fermat-style cells such as `p = 65537`.

This suggests the next honest analytic target is not another raw-frequency
adapter.  It is one of:

- a large-index gate with an explicit exceptional-structure exclusion;
- a higher `Kquot` or later cutoff `tau`, paired with a re-optimized weighted
  budget;
- a structural theorem explaining the Fermat/generalized-Fermat quotient spike
  family and isolating it from prize-scale parameters.

No closure is claimed here.  The probe narrows the admissible constant regime
for the parameterized quotient-tail route.
