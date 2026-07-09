# #466 R291 n=128 moving tail-rank caps

## Question

R290 showed that the fixed `tailRank <= 8192` cap is too rigid in
`M=20001..30000`: the residual has mass `0.20011545`, and its old constants
`tailX < 2`, `fineRatio < 0.80` drift.

R291 tests whether the residual is an artifact of using the wrong cap:

```text
fixed caps: 8192, 12000, 16384
moving caps: M/4, M/3, M/2
```

## Command

```bash
python3 scripts/probes/probe_r291_n128_moving_tailrank_caps.py \
  --min-index 20001 --max-index 30000 \
  --progress-every-primes 120 --progress-every-seconds 30 --top 32
```

## Result

```text
R291 n=128 moving tail-rank caps M=[20001,30000] highRatio>=0.75
primes=1311 candidateRows=2811 moderateRows=1602 highRows=1438
highMass=3.10265432
```

Residual by cap:

```text
cap          count mass      share
fixed:8192   237  0.200115  0.064498
fixed:12000   63  0.045033  0.014514
fixed:16384    0  0.000000  0.000000
m/4          403  0.383438  0.123584
m/3          228  0.197014  0.063498
m/2           36  0.026323  0.008484
```

The fixed dyadic cap `16384` absorbs every high-fineRatio row in this window.
The moving fractional caps are not the right shape: `M/4` and `M/3` are worse
than the original `8192`, and even `M/2` leaves a small residual.

## Interpretation

The R290 boundary drift is not evidence for a new analytic component.  It is
mostly an artifact of using a fixed cap that was one dyadic scale too small.

The better empirical law is:

```text
M = 512..12000:
  high-fineRatio branch satisfies tailRank <= 8192.

M = 12001..30000:
  high-fineRatio branch satisfies tailRank <= 16384.
```

This suggests a dyadic shoulder cap rather than a fractional moving cap:

```text
tailRank <= 2^ceil(log2 M) / 2
```

or, more cautiously for the scanned ranges:

```text
tailRank <= 2^14 for M <= 30000.
```

The dyadic form fits the tower-coherence story better than `M/c`: high-ratio
rows are controlled by a rank shoulder at the next dyadic scale, not by a fixed
fraction of the quotient length.

## Next target

Stress `fixed:16384` beyond `M=30000`.  If it fails, test the next dyadic cap
`32768`.  The proof-shaped conjecture should be phrased as a dyadic shoulder
ladder:

```text
HighFineRatioShoulder128:
  on a dyadic M-window, all high-fineRatio moderate rows lie below
  the corresponding dyadic tail-rank shoulder, with no separate boundary
  residual after choosing the right shoulder scale.
```

