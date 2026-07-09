# #466 R295 n=128 dyadic shoulder to 80k

## Question

R294 showed that `tailRank <= 40960` captures all high-fineRatio moderate rows
in `M=50001..65000`.  R295 tests the next window:

```text
M=65001..80000
caps: 40960, 49152, 57344, 65536, M/2
```

## Command

```bash
python3 scripts/probes/probe_r291_n128_moving_tailrank_caps.py \
  --min-index 65001 --max-index 80000 \
  --caps fixed:40960 fixed:49152 fixed:57344 fixed:65536 m/2 \
  --progress-every-primes 120 --progress-every-seconds 30 --top 32
```

## Result

```text
R291 n=128 moving tail-rank caps M=[65001,80000] highRatio>=0.75
primes=1865 candidateRows=7142 moderateRows=3858 highRows=3577
highMass=2.90541837
```

Residual by cap:

```text
cap          count mass      share
fixed:40960    7  0.001701  0.000585
fixed:49152    0  0.000000  0.000000
fixed:57344    0  0.000000  0.000000
fixed:65536    0  0.000000  0.000000
m/2           42  0.011165  0.003843
```

The previous cap `40960` leaks only seven tiny boundary rows.  The next cap
`49152` captures every high-fineRatio row in the window.

Worst row beyond `40960`:

```text
mass       fRatio  X128    F128    topR  tailR  topX    tailX   M      p
0.00026430 0.7513  12.106  10.851  15    41237  14.442  1.255   78036  9988609
```

## Interpretation

The shoulder ladder extends:

```text
M =   512..12000: tailRank <= 8192
M = 12001..30000: tailRank <= 16384
M = 30001..40000: tailRank <= 24576
M = 40001..50000: tailRank <= 32768
M = 50001..65000: tailRank <= 40960
M = 65001..80000: tailRank <= 49152
```

Again, rows escaping the previous cap are tiny-tail and barely above the
`0.75` high-ratio threshold:

```text
tailRank > 40960:
  count = 7,
  mass = 0.001701,
  worst mass = 0.00026430,
  max tailX = 1.2817,
  max fineRatio = 0.7554.
```

The cap sequence after the early windows is now a very regular `+8192` ladder.
The previous-cap boundary is shrinking in mass and amplitude as `M` grows.

## Next target

Convert the empirical ladder into a candidate statement:

```text
cap(M) = 8192 * ceil((M - 1) / 15000) ?  -- rough window fit
```

and test it directly as a moving piecewise cap on the union range
`M=12001..80000`.  The useful proof target is no longer a fixed cap, but a
monotone shoulder envelope whose failures one rung below are tiny-tail rows.

