# #466 R288 n=128 high-fineRatio tail-rank residual

## Question

R287 refuted the simple `topRank <= 8` certificate for the n=128 moderate
high-fineRatio branch, but found that `tailRank <= 8192` captures almost all
continuation mass:

```text
highMass = 2.46529551
tailRank <= 8192 mass = 2.433738
missing = 0.031558
```

R288 isolates the complementary residual:

```text
moderate := fine64best < 8 and X64max < 16
high     := fine128 / X64best >= 0.75
residual := high and tailRank > 8192
```

The hypothesis is that this is not another shoulder, but a tiny-tail/deep-tail
event with a small rowwise cap.

## Command

```bash
python3 scripts/probes/probe_r288_n128_high_fineratio_tailrank_residual.py \
  --min-index 12001 --max-index 20000 \
  --progress-every-primes 100 --progress-every-seconds 30 --top 24
```

## Result

```text
R288 n=128 high-fineRatio tail-rank residual M=[12001,20000] tailRank>8192
primes=1114 candidateRows=1542 moderateRows=891 highRows=792
highMass=2.46529551
residualRows=29 residualMass=0.03155764 residualShare=0.01280075
maxTailX=1.596075 maxTopRank=29 maxTailRank=10175
```

Every residual row has tiny tail value:

```text
tailX < 2:  count=29 mass=0.031558 share=1.000000
tailX < 1:  count=0  mass=0
```

The residual sits right above the high-ratio threshold:

```text
fineRatio >= 0.80: count=0 mass=0
```

Worst residual rows:

```text
mass       fRatio  X128    F128    topR  tailR  topX    tailX   M      p
0.00141443 0.7562  12.682  11.319  2     8243   14.968  1.363   16839  2155393
0.00136057 0.7549  12.966  11.586  4     9026   15.348  1.380   18794  2405633
0.00128807 0.7502  12.311  11.045  2     8838   14.723  1.266   16854  2157313
0.00128450 0.7673  12.536  11.078  3     8228   14.437  1.458   17880  2288641
0.00121025 0.7568  11.828  10.551  7     8306   13.941  1.276   15896  2034689
```

## Conclusion

R288 strengthens the R287 replacement target.

The high-fineRatio branch should be split as:

```text
1. tailRank <= 8192:
   the main balanced/moderate-rank shoulder;

2. tailRank > 8192:
   a tiny-tail boundary layer with
     tailX < 2,
     fineRatio < 0.80,
     row mass <= 0.001415
   in the scanned continuation window.
```

This is a proof-shaped split because the residual no longer has the balanced
two-child geometry.  It is a top child plus very deep, very small aligned tail
whose fineRatio is just barely above `0.75`.

Updated n=128 moderate branch map:

```text
low-fineRatio (<0.75):
  finite exception p=231169 plus diffuse deep-tail tax;

high-fineRatio (>=0.75):
  tailRank <= 8192 balanced shoulder;
  tailRank > 8192 tiny-tail boundary layer.
```

