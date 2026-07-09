# #466 R287 n=128 high-fineRatio envelope

## Question

R286 strengthened the low-fineRatio split: after the finite row `p=231169`,
the `fine128 / X64best < 0.75` moderate branch has individually tiny rows.

This probe tests the remaining moderate branch:

```text
moderate := fine64best < 8 and X64max < 16
high     := fine128 / X64best >= 0.75
```

The prior top-tail picture suggested that dangerous rows might be captured by
`topRank <= 8` plus a tail-value lower bound.  R287 asks whether that envelope
survives in the continuation window.

## Command

```bash
python3 scripts/probes/probe_r287_n128_high_fineratio_envelope.py \
  --min-index 12001 --max-index 20000 \
  --progress-every-primes 100 --progress-every-seconds 30 --top 24
```

## Result

```text
R287 n=128 high-fineRatio envelope M=[12001,20000] highRatio>=0.75
primes=1114 candidateRows=1542 moderateRows=891 highRows=792
highMass=2.46529551
```

Moderate fineRatio buckets:

```text
[0.00,0.75): count=99  mass=0.111018 worst=0.001790
[0.75,0.85): count=279 mass=0.439587 worst=0.004536
[0.85,0.90): count=174 mass=0.404873 worst=0.012931
[0.90,0.95): count=169 mass=0.552628 worst=0.014304
[0.95,inf):  count=170 mass=1.068207 worst=0.034745
```

The old top-rank envelope is false in this wider continuation window:

```text
topRank <= 8 captures 0.838250 / 2.465296
topRank <= 16 captures 1.496550 / 2.465296
```

Worst high-ratio rows escaping `topRank <= 8`:

```text
mass       fRatio  X128    F128    topR  tailR  topX    tailX   M      p
0.02052643 1.0000  24.044  12.181  13    18     12.181  11.863  19872  2543617
0.01818736 1.0001  22.906  11.457  17    18     11.457  11.449  16875  2160001
0.01702235 0.9998  21.686  11.106  17    21     11.108  10.580  13290  1701121
0.01671143 0.9544  21.574  10.535  17    25     11.039  10.537  13164  1684993
0.01480151 0.9839  22.584  13.414  10    94     13.634  9.170   19131  2448769
```

Tail-rank caps are much better aligned with the data:

```text
tailRank <= 512:  mass=1.038368 missing=1.426928
tailRank <= 1024: mass=1.391497 missing=1.073799
tailRank <= 2048: mass=1.742490 missing=0.722805
tailRank <= 4096: mass=2.152589 missing=0.312707
tailRank <= 8192: mass=2.433738 missing=0.031558
```

The high-ratio rows with tiny tail value exist, but they are individually
small:

```text
tailX < 2 worst mass = 0.00255837
tailX < 4 worst mass = 0.00507203
```

## Conclusion

R287 refutes the naive moderate high-fineRatio certificate:

```text
high branch != topRank <= 8 + aligned tail.
```

The high branch is a wider shoulder.  Its largest continuation rows are often
two moderate-rank children with nearly equal size and nearly full fine gain,
for example ranks `(13,18)`, `(17,18)`, `(17,21)`, `(17,25)`.

The replacement target should be:

```text
HighFineRatioShoulder(128):
  split by tailRank <= 8192, plus
  a residual tiny-tail envelope for tailX < 4 / tailRank > 8192.
```

This is a sharper theorem target than R273/R274:

```text
moderate low-fineRatio:
  finite exception p=231169 plus diffuse deep-tail tax;

moderate high-fineRatio:
  balanced/moderate-rank shoulder controlled by tailRank,
  not by topRank alone;

inherited:
  recursive resonance tree.
```

