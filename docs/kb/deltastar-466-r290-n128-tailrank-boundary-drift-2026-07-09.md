# #466 R290 n=128 tail-rank boundary drift

## Question

R288/R289 suggested a sharp high-fineRatio boundary layer:

```text
high := moderate and fine128 / X64best >= 0.75
residual := high and tailRank > 8192
```

For `M=12001..20000`, every residual row satisfied:

```text
tailX < 2
fineRatio < 0.80
worst mass = 0.00141443
```

R290 stress-tests whether those constants survive in the next window.

## Command

```bash
python3 scripts/probes/probe_r288_n128_high_fineratio_tailrank_residual.py \
  --min-index 20001 --max-index 30000 \
  --progress-every-primes 120 --progress-every-seconds 30 --top 32
```

## Result

```text
R288 n=128 high-fineRatio tail-rank residual M=[20001,30000] tailRank>8192
primes=1311 candidateRows=2811 moderateRows=1602 highRows=1438
highMass=3.10265432
residualRows=237 residualMass=0.20011545 residualShare=0.06449814
maxTailX=2.223663 maxTopRank=24 maxTailRank=15560
```

The old constants drift:

```text
tailX < 2:      215 / 237 rows, mass=0.180916
tailX < 3:      237 / 237 rows, mass=0.200115
fineRatio >= .80: 49 rows, mass=0.040781
fineRatio >= .85: 0 rows, mass=0
```

Worst residual rows:

```text
mass       fRatio  X128    F128    topR  tailR  topX    tailX   M      p
0.00140574 0.7834  14.240  12.392  3     8709   15.819  1.847   25011  3201409
0.00134323 0.8004  14.670  12.546  4     8442   15.674  2.124   29147  3730817
0.00129491 0.7691  13.050  11.513  4     8735   14.968  1.537   20169  2581633
0.00129037 0.7826  14.059  12.245  3     9267   15.647  1.814   26045  3333761
0.00126693 0.7745  13.567  11.909  4     9385   15.376  1.658   23456  3002369
```

## Conclusion

The exact R288 boundary constants are refuted for `M>20000`:

```text
tailRank > 8192 does not imply tailX < 2.
tailRank > 8192 does not imply fineRatio < 0.80.
```

But the structural boundary law survives in a slightly looser form:

```text
tailRank > 8192 in M=20001..30000:
  tailX < 3,
  fineRatio < 0.85,
  topRank <= 24,
  row mass <= 0.001406.
```

The residual is still a low-amplitude boundary layer, not a new balanced
shoulder.  Its mass share increased from `0.0128` in `12001..20000` to
`0.0645` in `20001..30000`, so the proof target should allow a slowly growing
deep-tail boundary tax unless a moving cap replaces the fixed `8192`.

## Next target

Test a moving tail-rank cap such as

```text
tailRank <= floor(M / 2), floor(M / 3), floor(sqrt(M) * c), or fixed 16384
```

on the same `M=20001..30000` window.  The goal is to determine whether the
boundary layer is an artifact of the fixed `8192` cutoff, or whether it is a
real deep-tail component requiring its own analytic estimate.

