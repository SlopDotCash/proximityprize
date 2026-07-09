# δ* #466 — bulk distribution model check (2026-07-08)

## Hypothesis

R173 showed a stable bulk law for

```text
X_C = |η_C|² / σ².
```

R174 tests whether this can be explained by a simple exponential distribution,
and whether that model is strong enough to become the proof target.

Probe: `scripts/probes/probe_r174_bulk_distribution_model.py`.

## Result

Representative rows:

```text
n   p          kind        best_lambda max_ratio max_abs mean_abs r170_ratio
--------------------------------------------------------------------------------------------
32  32993      spike       1           473.5833  0.1497  0.0221   0.5098
64  16778497   spike       1           73.2559   0.1246  0.0165   0.5470
128 268437889  control     1           74.0369   0.1258  0.0168   0.5442
256 16777729   control     1           69.5342   0.1262  0.0168   0.5459
512 262657     high-order  1           317.2608  0.0880  0.0128   0.5540
```

Bulk comparison:

```text
n=128 p=268437889
  exp1:    T0.5 0.481/0.607, T1 0.318/0.368, T1.5 0.221/0.223,
           T2 0.158/0.135, T3 0.083/0.050, T4 0.045/0.018
  exp0.75: T0.5 0.481/0.687, T1 0.318/0.472, T1.5 0.221/0.325,
           T2 0.158/0.223, T3 0.083/0.105, T4 0.045/0.050
```

Domination-prefactor barrier.  For a candidate survival theorem

```text
P[X ≥ T] ≤ A_λ exp(-λT)
```

the exact observed minimum prefactor is
`A_λ = sup_T P[X≥T] exp(λT)`.  The same probe reports:

```text
n   p          kind        A.25 A.35 A.43 A.50 A.60 A.75 A1
-----------------------------------------------------------------------
32  32993      spike       1    1    1.91 6.55 38.2 539   4.43e4
64  16778497   spike       1    1    1    4.03 58.8 3.68e3 3.64e6
128 268437889  control     1    1    1    1    1.71 44.4  1.60e4
256 16777729   control     1    1    1    1    1    7.41  462
512 262657     high-order  1    1    2.04 6.32 31.8 360   2.05e4
```

So the strong prize-shaped domination `λ≈1` is already false with any
constant-size prefactor on small exact spectra: sparse high-tail spikes force
`A_1` from hundreds to millions.  The viable envelope lives near
`λ≈1/4..0.43`; trying to prove a full exponential(1) tail would chase a false
statement.

## Verdict

The dyadic bulk resembles an exponential(1) tail up to roughly `T≈1.5`, but
the high tail is much heavier.  A theorem claiming full exponential(1)
stochastic domination is false in the relevant tail range.

The proof target should be split:

```text
Bulk:     prove a coarse exponential-like concentration, e.g. N(1) ≤ 0.5M.
High tail: prove the slower envelope N(T) ≤ (3/4)M exp(-T/4).
```

This explains why the R170 envelope works: it is intentionally much looser
than the bulk law at small `T`, but slow enough to tolerate the exceptional
high-tail cosets.

Honest consequence for the prize: the R168/R170 tail-envelope route is a
credible concentration bridge and may prove a robust constant-factor
Gauss-period bound, but by itself it cannot deliver the sharp prize constant
unless it is coupled to an additional structural theorem that removes or
separately prices the sparse high-tail spikes.  The next viable hypothesis is
therefore a two-component law: exponential(1)-like bulk plus a separately
bounded spike budget, not a single global exponential(1) envelope.
