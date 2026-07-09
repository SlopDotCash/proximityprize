# #466 R293 n=128 dyadic shoulder to 50k

## Question

R292 found that `tailRank <= 24576` captures all high-fineRatio moderate rows
in `M=30001..40000`, while `16384` leaks a tiny boundary.  R293 tests the next
window:

```text
M=40001..50000
caps: 24576, 32768, 40960, M/2
```

## Command

```bash
python3 scripts/probes/probe_r291_n128_moving_tailrank_caps.py \
  --min-index 40001 --max-index 50000 \
  --caps fixed:24576 fixed:32768 fixed:40960 m/2 \
  --progress-every-primes 120 --progress-every-seconds 30 --top 32
```

## Result

```text
R291 n=128 moving tail-rank caps M=[40001,50000] highRatio>=0.75
primes=1257 candidateRows=4055 moderateRows=2219 highRows=2013
highMass=2.36500551
```

Residual by cap:

```text
cap          count mass      share
fixed:24576   14  0.005552  0.002347
fixed:32768    0  0.000000  0.000000
fixed:40960    0  0.000000  0.000000
m/2           48  0.020696  0.008751
```

`24576` now leaks, but only barely.  `32768` captures every high-fineRatio row
in the whole window.

Worst rows beyond `24576`:

```text
mass       fRatio  X128    F128    topR  tailR  topX    tailX   M      p
0.00045641 0.7505  12.505  11.217  7     25795  14.947  1.288   49925  6390401
0.00042055 0.7548  12.177  10.882  9     25597  14.418  1.295   49916  6389249
0.00041222 0.7521  11.832  10.599  10    25119  14.092  1.233   46724  5980673
0.00041164 0.7540  11.800  10.553  10    24714  13.997  1.247   46416  5941249
0.00041012 0.7611  12.082  10.737  12    24730  14.108  1.344   49985  6398081
```

## Interpretation

The dyadic-shoulder picture survives:

```text
M =   512..12000: tailRank <= 8192
M = 12001..30000: tailRank <= 16384
M = 30001..40000: tailRank <= 24576
M = 40001..50000: tailRank <= 32768
```

The previous cap leaks only a tiny boundary:

```text
tailRank > 24576:
  count = 14,
  mass = 0.005552,
  worst mass = 0.00045641,
  max tailX = 1.3444,
  max fineRatio = 0.7676.
```

This keeps reinforcing the same law: when a shoulder cap starts leaking, its
escape rows are tiny-tail and barely above the `0.75` high-ratio threshold.
The next cap absorbs them completely.

## Next target

Stress `32768` on `M=50001..65000`.  If it leaks, test `40960` and `49152`.
The emerging proof target is a monotone rank-shoulder envelope with a small
boundary layer at the previous cap:

```text
HighFineRatioShoulder128(M):
  all high-fineRatio moderate rows lie under the active shoulder cap;
  rows escaping the previous cap have tailX about 1.2-1.6 and tiny mass.
```

