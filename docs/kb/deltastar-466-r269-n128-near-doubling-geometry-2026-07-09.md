# #466 R269 n=128 near-doubling geometry

## Question

R268 showed that the moderate-ancestor branch is better detected by

```text
fine128 / X64best ≈ 0.75--1.00
```

than by the crude ratio `X128 / X64best`.  This probe tests a local geometric
hypothesis for that branch:

```text
near-doubling = same phase + balanced children.
```

The script measures the top-level join `eta128 = a + b`, recording

```text
balance = min(X64(a), X64(b)) / max(X64(a), X64(b))
phase   = Re(a conj(b)) / (|a| |b|).
```

## Command

```bash
python3 scripts/probes/probe_r269_n128_near_doubling_geometry.py \
  --min-index 512 --max-index 6000 --chunk 4096 \
  --top-per-row 4 --min-fine128 10 \
  --fine-ratio-cut 0.75 --top 25
```

## Result

Using the corrected ancestor fine layer `fine64 = X64 - lift(X32)`:

```text
rows=233
moderate=149
near=136
mass moderate=2.15759729
mass near=1.86531933
```

The phase condition is rigid:

```text
phase median=1.000000000
phase min=1.000000000

phase >= 0.999: count=136 mass=1.865319
```

But balanced children are not necessary:

```text
balance median=0.251003
balance min=0.086350

balance >= 0.25: count=69 mass=1.334517
balance >= 0.40: count=21 mass=0.700314
balance >= 0.60: count=4  mass=0.280035
balance >= 0.80: count=2  mass=0.176659
```

Representative near rows:

```text
p=288257 M=2252 mass=0.129143
X128=22.69 fine128=10.71 children=(11.99,10.72)
balance=0.894 phase=1.0 fineRatio=0.893

p=183041 M=1430 mass=0.076779
X128=18.79 fine128=12.77 children=(6.02,13.51)
balance=0.446 phase=1.0 fineRatio=0.945

p=95233 M=744 mass=0.055211
X128=14.86 fine128=11.25 children=(3.61,12.60)
balance=0.286 phase=1.0 fineRatio=0.893

p=198529 M=1551 mass=0.025686
X128=14.74 fine128=11.97 children=(2.77,14.17)
balance=0.196 phase=1.0 fineRatio=0.845
```

## Conclusion

The balanced-annulus hypothesis is refuted.  Near-doubling is not primarily
`same phase + equal magnitudes`; it is an **oriented same-phase join** where the
unlifted child supplies most of the fine gain.  The phase part is extremely
clean, but the magnitude ratio ranges widely.

The theorem-shaped replacement is:

```text
large moderate n=128 branch
  -> top-level children are same-phase,
  -> the unlifted child is large relative to the lifted child,
  -> and the oriented fine gain is close to the unlifted child's contribution.
```

So the next useful count is not an annulus count.  It should count oriented
same-phase pairs `(a,b)` where the non-lifted child is large and phase-aligned
with the lifted child.
