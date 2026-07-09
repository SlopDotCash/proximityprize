# #466 R292 n=128 dyadic shoulder next window

## Question

R291 found that the high-fineRatio moderate branch in `M=20001..30000` is
fully captured by `tailRank <= 16384`.  R292 asks whether the same cap survives
one more window, or whether the shoulder must advance.

## Command

```bash
python3 scripts/probes/probe_r291_n128_moving_tailrank_caps.py \
  --min-index 30001 --max-index 40000 \
  --caps fixed:16384 fixed:24576 fixed:32768 m/2 \
  --progress-every-primes 120 --progress-every-seconds 30 --top 32
```

## Result

```text
R291 n=128 moving tail-rank caps M=[30001,40000] highRatio>=0.75
primes=1329 candidateRows=3565 moderateRows=2061 highRows=1866
highMass=2.75728006
```

Residual by cap:

```text
cap          count mass      share
fixed:16384   88  0.048564  0.017613
fixed:24576    0  0.000000  0.000000
fixed:32768    0  0.000000  0.000000
m/2           43  0.022987  0.008337
```

The `16384` cap leaks in this window, but `24576` already captures every
high-fineRatio row.  The full `32768` dyadic jump is not needed in this scan.

Worst rows beyond `16384`:

```text
mass       fRatio  X128    F128    topR  tailR  topX    tailX   M      p
0.00079469 0.7581  13.469  12.002  8     16680  15.833  1.467   36491  4670849
0.00074382 0.7588  13.293  11.838  3     17114  15.602  1.455   37307  4775297
0.00073362 0.7596  13.497  12.011  3     17829  15.813  1.486   39806  5095169
0.00072455 0.7617  13.371  11.876  7     17389  15.590  1.495   39057  4999297
0.00069611 0.7654  12.925  11.441  12    16433  14.948  1.483   36357  4653697
```

## Interpretation

The high-fineRatio shoulder cap is growing, but the escaping rows remain a
tiny-tail boundary:

```text
tailRank > 16384:
  tailX <= 1.6118,
  fineRatio <= 0.7923,
  topRank <= 20,
  worst mass <= 0.000795.
```

The empirical ladder is now:

```text
M =   512..12000: tailRank <= 8192
M = 12001..30000: tailRank <= 16384
M = 30001..40000: tailRank <= 24576
```

This refines the naive dyadic-power hypothesis.  The shoulder scale appears to
advance more smoothly than powers of two, while still living on a dyadic/tower
rank geometry rather than a simple fraction of `M`.

## Next target

Test whether `24576` survives to `M=50000`, and compare against `32768`.
If `24576` fails but `32768` holds, the practical certificate may be a
piecewise dyadic-shoulder ladder with generous slack:

```text
tailRank <= 8192, 16384, 24576, 32768, ...
```

The analytic task is to replace these empirical caps with a monotone shoulder
envelope for aligned tail partners around high-fineRatio joins.

