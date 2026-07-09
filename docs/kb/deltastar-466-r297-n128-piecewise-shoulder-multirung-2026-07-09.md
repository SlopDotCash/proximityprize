# #466 R297 n=128 piecewise shoulder multi-rung check

## Question

R296 introduced the formula cap:

```text
cap(M) = 8192 * ceil((M + 10000) / 15000)
```

Smoke checks showed no formula escapes near `M=12001` and `M=74500..80000`.
R297 tests a larger multi-rung chunk:

```text
M=30001..50000
```

This range crosses from formula cap `24576` to `32768`.

## Command

```bash
python3 scripts/probes/probe_r296_n128_piecewise_shoulder_cap.py \
  --min-index 30001 --max-index 50000 \
  --progress-every-primes 160 --progress-every-seconds 30 --top 32
```

## Result

```text
R296 n=128 piecewise shoulder cap M=[30001,50000]
cap=8192*ceil((M+10000)/15000)
primes=2586 candidateRows=7620 moderateRows=4280 highRows=3879
highMass=5.12228557
```

Residual summary:

```text
formula residual:
  count=0
  mass=0

previous-cap residual:
  count=37
  mass=0.018509
  share=0.003613
  worstMass=0.000665 at M=30944 p=3960833
  maxTailX=1.3665
  maxFineRatio=0.7688
  maxTailRank=26228
```

Worst previous-cap boundary rows:

```text
mass       fRatio  X128    F128    topR  tailR  cap    tailX   M      p
0.00066533 0.7503  12.099  10.854  7     16444  24576  1.245   30944  3960833
0.00061095 0.7579  12.204  10.877  5     17217  24576  1.327   34595  4428161
0.00060721 0.7635  12.070  10.704  9     16529  24576  1.366   33665  4309121
0.00060050 0.7598  11.986  10.664  12    16790  24576  1.322   33332  4266497
0.00060001 0.7595  12.040  10.716  9     17005  24576  1.324   33812  4327937
```

## Conclusion

The formula cap survives a genuine multi-rung check:

```text
M=30001..50000:
  tailRank <= 8192 * ceil((M + 10000) / 15000)
```

for every scanned high-fineRatio moderate row.

The previous-cap residual has the same tiny-tail shape observed in R291--R296:

```text
tailX <= 1.3665,
fineRatio <= 0.7688,
row mass <= 0.000665.
```

This strengthens the candidate theorem:

```text
PiecewiseShoulder128:
  high-fineRatio moderate rows satisfy the formula cap.

PreviousShoulderBoundary128:
  rows escaping one rung below are tiny-tail and barely high-ratio.
```

## Next target

Run the formula cap over:

```text
12001..30000
50001..80000
```

The second chunk is more important because it tests caps `40960` and `49152`
under the same formula.

