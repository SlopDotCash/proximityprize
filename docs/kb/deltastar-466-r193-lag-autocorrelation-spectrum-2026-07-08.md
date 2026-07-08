# #466 R193: lag-autocorrelation spectrum

Status: exploratory probe.

R192 reduced the R191 product-MGF law to the half-turn covariance of

```text
f_j = exp((|eta_j|^2 / sigma^2) / 8)
```

on the quotient coset cycle. R193 asks whether the half-turn is special or whether `f` has small
autocorrelation at many lags. If many nonzero lags have small correlation, the proof target may be
a general mixing/equidistribution theorem for the observable rather than a bespoke dyadic symmetry.

Probe:

```bash
python3 scripts/probes/probe_r193_lag_autocorrelation_spectrum.py
```

Interpretation:

- `halfCorr` is the R192 dyadic lag.
- `maxAbsCorr@lag` is the largest absolute correlation among the selected lags.
- If adjacent/small lags are not small but half-turn is, the proof must exploit the exact dyadic
  involution. If all sampled lags are small, a more general quotient-mixing route is plausible.

## Run result

```text
n p M mean var halfCorr maxAbsCorr@lag selected_lags(corr)
16  1048609    65538    1.151858 6.064127e-02 -0.0004 +0.0132@1
32  16778497   524328   1.153239 6.949902e-02 +0.0045 +0.0045@262164
64  16778497   262164   1.154140 8.187221e-02 -0.0009 +0.0016@2
128 268437889  2097171  1.154323 7.768040e-02 -0.0002 -0.0005@2
256 16777729   65538    1.154376 7.644908e-02 -0.0019 +0.0129@13
```

Selected lag correlations are all small. The half-turn is not uniquely special; the observable
appears quotient-mixing at many lags. This makes the strongest proof hypothesis:

```text
For f_j = exp(X_j/8), all nonzero quotient lags have |Cov_h(f)| <= o(1),
or at least the dyadic half-turn has Cov <= K with K < 2 - B^2.
```

The second form is very slack. With `B^2` near `4/3`, any `K < 2/3` closes the R168 product
budget. The measured `K` is about `10^-4`.

Lean consumer:

`_R193CovarianceSlackConsumer.lean` proves the deterministic implication

```text
mean(f), mean(g) <= B
Cov(f,g) <= K
B^2 + K <= A
----------------
avg(f*g) <= A.
```

For R168 take `A = 2`. Thus the remaining analytic problem is now a deliberately loose
one-level MGF mean bound plus a covariance bound, not exact Gaussianity.
