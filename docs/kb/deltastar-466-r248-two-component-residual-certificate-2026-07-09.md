# #466 R248: two-component residual certificate scan

Date: 2026-07-09

## Question

R247 refutes literal monotonicity of

```text
H(theta) = S(theta) exp(theta/2).
```

R248 asks whether the residual CDF theorem can still be split into two simpler
lemmas:

1. a first-band bulk cap at `theta = 0.75`, and
2. a high-tail half-rate cap above a cutoff `kappa > 0.75`.

Command:

```bash
python3 scripts/probes/probe_r248_two_component_residual_certificate.py --cache-only
```

## Output

```text
cutoff  bulk_S(0.75) high_C   high_theta
0.875   0.412121     0.584933 0.929961
1.000   0.412121     0.560092 1.000391
1.125   0.412121     0.544554 1.128246
1.250   0.412121     0.532976 1.292202
1.500   0.412121     0.507281 1.560933
1.750   0.412121     0.483243 1.750067
2.000   0.412121     0.478367 2.006178
```

The high-tail side has good slack above `0.875`; compare the target
`C = 0.6012`.

But the first-band cap alone cannot bridge the interval `[0.75, kappa)`. For
example,

```text
0.412121 * exp(0.875/2) = 0.638...
```

which is already above the target constant. Monotonicity of raw survival is too
weak.

## Route update

The naive two-component certificate is insufficient. A viable proof split needs
one of:

- a short-band shape lemma for `0.75 <= theta <= 0.875`, or
- several explicit band caps, e.g. at `0.75`, `0.80`, `0.875`, then the
  high-tail half-rate certificate.

The good news is that the high-tail side is no longer knife-edge once the first
short band is handled.
