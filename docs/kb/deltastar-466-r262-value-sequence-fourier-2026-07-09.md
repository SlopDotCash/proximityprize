# #466 R262: value-sequence Fourier features

Date: 2026-07-09

## Question

R244 showed the first-band threshold sets are Fourier-uniform as subsets of the
quotient index group. R262 asks a different question: do the actual unsorted
value sequences `X_j` have low-mode Fourier features that predict the
micro-band obstruction?

Command:

```bash
python3 scripts/probes/probe_r262_value_sequence_fourier.py --cache-only
```

## Result

Worst micro-band rows:

```text
micro    S075     low8     low32    maxCoef  entropy  l2       n     p          M
0.601134 0.412121 0.00318  0.02000  0.08013  6.883    1.23303  512   760321     1485
0.601039 0.412056 0.00462  0.02415  0.08926  6.680    1.23009  512   620033     1211
0.600614 0.411765 0.01261  0.03682  0.09110  6.336    1.17910  512   417793     816
```

Correlations with the micro-band score:

```text
low8     -0.171890
low32    -0.198734
maxCoef  -0.272459
entropy  +0.203036
l2       -0.235053
```

## Route update

There is no useful low-mode value-wave explanation. The micro-band obstruction
is weakly associated with higher entropy and weaker Fourier peaks, not with a
smooth quotient-index wave.

This closes another tempting proof route: the direct cap is not likely to
follow from bounding a few low Fourier modes of the quotient value sequence.
