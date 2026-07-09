# #466 R294 n=128 dyadic shoulder to 65k

## Question

R293 showed that `tailRank <= 32768` captures all high-fineRatio moderate rows
in `M=40001..50000`.  R294 tests the next larger window:

```text
M=50001..65000
caps: 32768, 40960, 49152, 65536, M/2
```

## Command

```bash
python3 scripts/probes/probe_r291_n128_moving_tailrank_caps.py \
  --min-index 50001 --max-index 65000 \
  --caps fixed:32768 fixed:40960 fixed:49152 fixed:65536 m/2 \
  --progress-every-primes 120 --progress-every-seconds 30 --top 32
```

## Result

```text
R291 n=128 moving tail-rank caps M=[50001,65000] highRatio>=0.75
primes=1896 candidateRows=6868 moderateRows=3790 highRows=3455
highMass=3.35352153
```

Residual by cap:

```text
cap          count mass      share
fixed:32768   14  0.004025  0.001200
fixed:40960    0  0.000000  0.000000
fixed:49152    0  0.000000  0.000000
fixed:65536    0  0.000000  0.000000
m/2           73  0.023886  0.007123
```

The previous clean cap `32768` leaks only a tiny boundary.  The next cap
`40960` captures every high-fineRatio row in the window.

Worst row beyond `32768`:

```text
mass       fRatio  X128    F128    topR  tailR  topX    tailX   M      p
0.00034375 0.7509  12.318  11.046  7     32987  14.711  1.272   63266  8098049
```

## Interpretation

The high-fineRatio shoulder ladder continues:

```text
M =   512..12000: tailRank <= 8192
M = 12001..30000: tailRank <= 16384
M = 30001..40000: tailRank <= 24576
M = 40001..50000: tailRank <= 32768
M = 50001..65000: tailRank <= 40960
```

The rows escaping the previous cap remain uniformly tiny:

```text
tailRank > 32768:
  count = 14,
  mass = 0.004025,
  worst mass = 0.00034375,
  max tailX = 1.2906,
  max fineRatio = 0.7618.
```

This supports a monotone shoulder-envelope theorem: the active cap grows with
the index window, and previous-cap leaks are a negligible tiny-tail boundary
barely above the `0.75` high-ratio threshold.

## Next target

The empirical cap sequence now looks like:

```text
8192, 16384, 24576, 32768, 40960, ...
```

This is linear in blocks of `8192` after the first transition.  The next probe
should test `40960` versus `49152` on `M=65001..80000`, and then fit the cap as
a simple function of `M`-window index.  A likely certificate target is a
piecewise constant shoulder cap:

```text
cap(M) = 8192 * ceil((M + offset) / windowWidth)
```

with an accompanying tiny-boundary estimate for rows escaping `cap(M)-8192`.

