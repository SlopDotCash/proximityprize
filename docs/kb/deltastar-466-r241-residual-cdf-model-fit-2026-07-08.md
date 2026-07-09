# #466 R241: trim-five residual CDF model fit

Date: 2026-07-08

## Question

After the top-five quotient-orbit split from R231/R237, R238 identified the
knife-edge residual obligation

```text
#{X_res >= theta} / M <= 0.6012 * exp(-theta/2),  theta >= 0.75.
```

R241 tests whether this half-rate envelope is an arbitrary fit, or whether the
cached exact quotient spectra force it.

Command:

```bash
python3 scripts/probes/probe_r241_residual_cdf_model_fit.py --cache-only
```

Cache: `.cache/proximity-r231`, 1499 exact spectra with
`n in {256,512,1024}`, `M >= 512`.

## Empirical CDF edge

The worst residual survival after deleting the top five is concentrated in the
first band.

```text
theta   surv      half_C    slack     count  M      n     p
0.750   0.412121  0.599633  0.001567  612    1485   512   760321
0.800   0.395541  0.590078  0.011122  479    1211   512   620033
0.875   0.375000  0.580811  0.020389  297    792    256   202753
1.000   0.339646  0.559982  0.041218  269    792    256   202753
1.250   0.283544  0.529730  0.071470  336    1185   512   606721
1.500   0.237189  0.502129  0.099071  162    683    512   349697
2.000   0.175439  0.476892  0.124308  110    627    1024  642049
```

At the exact R238 endpoint the worst required half-rate constant is slightly
larger:

```text
rate=0.500 A_req=0.601109 theta=0.756650 count=336 M=816 n=512 p=417793
```

Thus `C = 0.6012` has only about `9.1e-5` local slack for the residual tail
certificate, but the slack grows quickly above the first band.

## Exponential rate scan

For envelopes `survival(theta) <= A exp(-rate theta)`, `theta >= 0.75`:

```text
rate    A_req     budget_proxy  theta
0.250   0.497509  1.649799      0.756650
0.375   0.546862  1.100781      0.756650
0.500   0.601109  0.826272      0.756650
0.625   1.618257  1.620287      11.957514
0.750   7.477409  5.680666      12.522025
1.000   171.124698 80.833584    12.522025
```

The half-rate is not cosmetic: increasing the rate above `1/2` makes rare
post-trim spikes dominate the required constant. Decreasing the rate reduces
the constant but loses too much integrated MGF budget. The top-five route is
therefore naturally pinned to the `exp(-theta/2)` residual survival law.

## Distributional model check

Gamma laws with mean one are qualitatively close but cannot be used as a clean
upper model without an added correction:

```text
shape  max(empirical - gamma)
0.500  +0.025645
0.550  +0.019596
0.600  +0.021369
0.650  +0.023373
0.700  +0.025546
1.000  +0.040103
```

The best tested gamma shape is near `k = 0.55`, but it still underestimates the
first band. This makes the gamma model useful as intuition only; the theorem
target should be the direct residual CDF envelope.

## Route update

The surviving certificate architecture is now:

1. Pay the top five quotient-orbit values exactly.
2. Prove a direct trim-five residual CDF theorem
   `#{X_res >= theta} <= 0.6012 M exp(-theta/2)` for `theta >= 0.75`.
3. Handle the two `n=128` exceptions by direct finite certificates from R234/R235.

R241 strengthens the case that step 2 is the correct local theorem, not a
numerical accident or a replaceable gamma/mean-field approximation.
