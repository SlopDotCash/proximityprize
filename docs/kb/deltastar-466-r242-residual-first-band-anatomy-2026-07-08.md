# #466 R242: trim-five first-band anatomy

Date: 2026-07-08

## Question

R238-R241 reduce the live top-five route to the first residual band:

```text
#{X_res >= theta} / M <= 0.6012 exp(-theta/2), theta >= 0.75.
```

R242 audits the rows that nearly saturate the `theta = 0.75` endpoint to decide
whether the obstruction is caused by remaining high spikes, coarse distribution
shape, or index-level arithmetic.

Command:

```bash
python3 scripts/probes/probe_r242_residual_first_band_anatomy.py --cache-only
```

## Worst rows

Top rows by `survival(0.75) * exp(0.75/2)`:

```text
half_C   frac     mean     var      q50      q70      q90      M/n      M      n     p
0.599633 0.412121 0.96965  1.52550  0.51308  1.10817  2.58498  2.9004   1485   512   760321
0.599538 0.412056 0.96497  1.51938  0.50355  1.09220  2.46777  2.3652   1211   512   620033
0.599114 0.411765 0.95986  1.39886  0.51236  1.08382  2.54916  1.5938   816    512   417793
0.593387 0.407828 0.94883  1.35981  0.53921  1.12866  2.33846  3.0938   792    256   202753
0.592774 0.407407 0.91977  1.22181  0.53085  1.07491  2.49553  1.0020   513    512   262657
```

The worst row has residual top order stats

```text
n=512 p=760321 M=1485 M/n=2.900391
8.918090 7.455100 7.406255 7.254037 7.207062 7.091757 6.851996 6.560226
```

but these remaining spikes are not the bottleneck for the first band.

## Correlation audit

Correlation with the first-band constant:

```text
frac     +1.000000
mean     +0.271516
second   -0.162889
var      -0.248298
q50      +0.659013
q60      +0.937485
q70      +0.656804
q80      +0.211673
q90      -0.202454
M/n      +0.101551
logM     +0.205058
```

The high residual tail (`q90`, variance, second moment) is weakly
anti-correlated with the first-band obstruction. The bottleneck is the middle
bulk, especially the 60th percentile. This also explains why R239 found low
moments vacuous: high moments look in the wrong place.

## Useful maxima

```text
q50=0.53921153 half_C=0.59338665 n=256 p=202753 M=792
q60=0.79048859 half_C=0.59963283 n=512 p=760321 M=1485
q70=1.16841260 half_C=0.54840427 n=512 p=368129 M=719
q80=1.75752225 half_C=0.52487357 n=256 p=249089 M=973
q90=2.96556905 half_C=0.53156971 n=512 p=463873 M=906
```

## Route update

The residual CDF theorem should be attacked as a middle-bulk theorem:

```text
after deleting the top five quotient values,
at most about 0.4122 M residual values can exceed 0.75.
```

Equivalently, one needs a robust upper bound on the trim-five 59th percentile.
The theorem should not be phrased as a remaining-spike classification or a
high-moment estimate; R242 shows those quantities do not govern the live
endpoint.
