# #466 R260: micro-band arithmetic features

Date: 2026-07-09

## Question

R259 says the direct micro-band cap

```text
S(0.75) <= 612 / 1485
```

is the right target. R260 asks whether the worst rows cluster in an arithmetic
subfamily of quotient indices `M` or primes `p = M n + 1`.

Command:

```bash
python3 scripts/probes/probe_r260_microband_arithmetic_features.py --cache-only
```

## Result

Worst rows:

```text
micro    S075     n     p          M
0.601134 0.412121 512   760321     1485
0.601039 0.412056 512   620033     1211
0.600614 0.411765 512   417793     816
0.594872 0.407828 256   202753     792
0.594258 0.407407 512   262657     513
```

Feature correlations with the micro-band score:

```text
logM       +0.203297
M          +0.170031
M/n        +0.098953
omegaM     +0.042315
Mmod8      -0.040630
Mmod3      -0.022711
lpfM       +0.017418
Mmod16     +0.014590
v2(M-1)    +0.003136
```

Worst by dyadic level:

```text
n=256  micro=0.59487197 S075=0.40782828 p=202753  M=792
n=512  micro=0.60113378 S075=0.41212121 p=760321  M=1485
n=1024 micro=0.59160586 S075=0.40558912 p=1355777 M=1324
```

Residue classes and factorizations are mixed. There is no obvious congruence,
smoothness, largest-prime-factor, or `v2(M±1)` explanation.

## Route update

The micro-band obstruction does not appear to be a small arithmetic subfamily
that can be carved out by simple index features. The direct theorem should be
distributional:

```text
for trim-five residual Gauss-period spectra on the main lane,
S(0.75) <= 612 / 1485.
```

Finite exception handling remains necessary for `n=128`, but the main-lane
worst rows are not explained by elementary arithmetic fingerprints.
