# #466 R296 n=128 piecewise shoulder cap

## Question

R291--R295 produced an empirical high-fineRatio shoulder ladder:

```text
M =   512..12000: tailRank <= 8192
M = 12001..30000: tailRank <= 16384
M = 30001..40000: tailRank <= 24576
M = 40001..50000: tailRank <= 32768
M = 50001..65000: tailRank <= 40960
M = 65001..80000: tailRank <= 49152
```

R296 turns this into an executable candidate cap:

```text
cap(M) = 8192 * ceil((M + 10000) / 15000)
```

This formula is intentionally a little generous around `M=20001..30000`, but it
matches the later rung advances and is simple enough to become a theorem target.

## Probe

New script:

```text
scripts/probes/probe_r296_n128_piecewise_shoulder_cap.py
```

It scans high-fineRatio moderate rows and records:

```text
formula residual: tailRank > cap(M)
prevCap residual: tailRank > cap(M) - 8192
```

The previous-cap residual is kept because R291--R295 repeatedly show that rows
escaping the previous rung are tiny-tail boundary rows.

## Smoke checks

Near the first transition:

```bash
python3 scripts/probes/probe_r296_n128_piecewise_shoulder_cap.py \
  --min-index 12001 --max-index 12200 \
  --progress-every-primes 10 --top 8
```

Result:

```text
cap=16384
formula residual: 0 rows, mass=0
prevCap residual: 0 rows, mass=0
```

Near the late `40960 -> 49152` transition:

```bash
python3 scripts/probes/probe_r296_n128_piecewise_shoulder_cap.py \
  --min-index 74500 --max-index 80000 \
  --progress-every-primes 120 --progress-every-seconds 30 --top 16
```

Result:

```text
R296 n=128 piecewise shoulder cap M=[74500,80000]
primes=688 candidateRows=2665 moderateRows=1415 highRows=1315
highMass=1.02202328

formula residual:
  count=0 mass=0

prevCap residual:
  count=7 mass=0.001701 share=0.001664
  worstMass=0.000264 at M=78036 p=9988609
  maxTailX=1.2817 maxFineRatio=0.7554 maxTailRank=42030
```

Worst previous-cap boundary rows:

```text
mass       fRatio  X128    F128    topR  tailR  cap    tailX   M      p
0.00026430 0.7513  12.106  10.851  15    41237  49152  1.255   78036  9988609
0.00026230 0.7536  12.161  10.879  19    41378  49152  1.282   79715  10203521
0.00024427 0.7514  11.677  10.466  16    41331  49152  1.211   75854  9709313
```

## Conclusion

The formula cap survived both smoke checks and reproduces the known boundary
shape:

```text
tailRank > cap(M):
  no observed high-fineRatio moderate rows in checked ranges.

tailRank > cap(M)-8192:
  tiny-tail boundary rows only.
```

This gives a clean theorem-shaped hypothesis:

```text
PiecewiseShoulder128:
  For n=128 high-fineRatio moderate joins,
  tailRank <= 8192 * ceil((M + 10000) / 15000).
```

The secondary boundary estimate is:

```text
PreviousShoulderBoundary128:
  Rows with tailRank > cap(M)-8192 have tailX about 1.2--1.6,
  fineRatio barely above 0.75, and tiny exp(X128/4)/M mass.
```

## Next target

Run the formula cap over the full union range `M=12001..80000`, or in chunks
that reuse the established windows:

```text
12001..30000
30001..50000
50001..80000
```

If the formula survives, the next proof task is to explain why aligned-tail
partners above this cap cannot supply enough `tailX` to make high-fineRatio
joins.

