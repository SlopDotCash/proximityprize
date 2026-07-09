# #466 R192: half-turn autocorrelation anatomy

Status: exploratory hypothesis.

R191's dyadic product-MGF residual can be rewritten as a half-turn autocorrelation on the quotient
cycle of child cosets. Let

```text
f_j = exp(X_j / 8),  X_j = |eta_j|^2 / mean(|eta|^2),  M=(p-1)/n.
```

The parent `μ_{2n}` product budget is

```text
(2/M) * sum_{0 <= j < M/2} f_j * f_{j+M/2}.
```

Thus

```text
productBudget = mean(f)^2 + halfTurnCov(f).
```

If `mean(f) -> sqrt(4/3)` and the half-turn covariance is non-positive or small, the R191
`4/3` law follows. This turns the product-MGF route into an explicit autocorrelation/Fourier
problem on the coset quotient.

Probe:

```bash
python3 scripts/probes/probe_r192_halfturn_autocorrelation.py
```

Potential proof target: show that for the dyadic half-turn `M/2`, the centered observable
`exp(|eta_j|^2/8) - mean` has bounded or negative autocorrelation. Fourier form:

```text
halfTurnCov = sum_ell (-1)^ell * |fhat_ell|^2
```

up to normalization, so the exact target is an even-vs-odd spectral-energy imbalance.

## Run result

```text
n p M mean mean^2 product cov corr evenE oddE topFourier(ell:frac)
16  1048609    65538    1.151858 1.326777 1.326750 -2.675454e-05 -0.0004 3.030726e-02 3.033401e-02
32  16778497   524328   1.153239 1.329960 1.330273 +3.129516e-04 +0.0045 3.490599e-02 3.459304e-02
64  16778497   262164   1.154140 1.332040 1.331968 -7.184675e-05 -0.0009 4.090018e-02 4.097203e-02
128 268437889  2097171  1.154323 1.332462 1.332460 -2.577991e-06 -0.0000 3.883891e-02 3.884148e-02
256 16777729   65538    1.154376 1.332583 1.332434 -1.490227e-04 -0.0019 3.815003e-02 3.829905e-02
```

Interpretation:

- The product budget is almost exactly `mean(f)^2`; the half-turn covariance is at the `10^-4`
  scale and changes sign.
- `mean(f)^2` approaches `4/3` from below, matching the `chi^2_1` MGF value
  `E exp(X/8) = sqrt(4/3)`.
- The even/odd half-turn energies are nearly equal. Therefore a proof can target either:
  a small covariance bound `cov <= 2 - mean^2`, which is very slack for the R168 consumer, or
  a sharper non-positive/near-zero covariance theorem if aiming for the exact `4/3` fixed point.

Lean consumer:

`_R192HalfTurnAutocorrelationConsumer.lean` proves the deterministic product-mean decomposition
and the sufficient implication:

```text
mean(f), mean(g) <= B and centeredProductMean(f,g) <= 0
  => avg(f*g) <= B^2.
```

For the exact R191 route one would take `B = sqrt(4/3)`. For the prize consumer it suffices to
prove a much weaker pair of bounds giving `avg(f*g) <= 2`.
