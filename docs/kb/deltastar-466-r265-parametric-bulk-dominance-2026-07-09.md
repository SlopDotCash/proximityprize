# #466 R265: parametric bulk dominance

Date: 2026-07-09

## Question

R255 showed the trim-five residual middle bulk lies below the `Exp(1)` q60.
R265 tests whether a simple mean-one Gamma or Weibull family can dominate the
observed low-bulk CDF envelope with theorem-friendly parameters.

Command:

```bash
python3 scripts/probes/probe_r265_parametric_bulk_dominance.py --cache-only
```

## Result

Empirical envelope:

```text
theta   Smax
0.500   0.516414
0.625   0.470960
0.750   0.412121
0.755   0.411765
0.800   0.395541
0.875   0.375000
1.000   0.339646
1.250   0.283544
```

Gamma mean-one envelopes:

```text
shape   minSlack theta@min
0.650   -0.008855 1.250
0.700   -0.006232 1.250
0.800   -0.002115 1.250
1.000   +0.002960 1.250
```

Gamma shape `0.7` gives comfortable slack near the micro-band:

```text
theta=0.750 model=0.428385 empirical=0.412121 slack=+0.016264
theta=0.800 model=0.409552 empirical=0.395541 slack=+0.014011
```

but fails at `theta=1.25`. The exponential shape `1.0` dominates the sampled
grid but is too loose for the R251 budget.

## Route update

Parametric dominance is useful intuition but not a certificate. The residual
bulk behaves roughly like a Gamma shape `0.65-0.8` near the micro-band, then
has a heavier upper residual tail. A single mean-one Gamma/Weibull law cannot
both:

1. preserve the tight micro-band budget, and
2. dominate the upper low-band envelope.

This reinforces the current split: prove the direct micro-band cap separately
from the high-tail half-rate certificate.
