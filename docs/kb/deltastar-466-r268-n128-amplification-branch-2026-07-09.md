# #466 R268 n=128 amplification branch

## Question

R267 found two n=128 coherent-path modes:

1. inherited high-fine n=64 ancestors;
2. amplified moderate n=64 ancestors.

This probe asks whether the second branch is captured by simple top-level
amplification ratios:

```text
ratio      = X128 / X64best
fineRatio  = fine128 / X64best.
```

Rows are split as inherited if `fine64 >= 8` or `X64 >= 16`; otherwise they are
called moderate.

## Command

```bash
python3 scripts/probes/probe_r268_n128_amplification_branch.py \
  --min-index 512 --max-index 6000 --chunk 4096 \
  --top-per-row 4 --min-fine128 10 \
  --ancestor-fine-cut 8 --ancestor-x-cut 16 --top 25
```

## Result

```text
rows=231
mass total=3.24063407
inherited mass=1.08303678
moderate mass=2.15759729
```

Simple ratio thresholds only partially isolate the moderate branch:

```text
moderate_ratio >= 1.25: count=41 mass=1.172850 worstMass=0.246187
moderate_ratio >= 1.50: count=7  mass=0.655594 worstMass=0.246187
moderate_ratio >= 1.75: count=2  mass=0.176659 worstMass=0.129143
moderate_ratio >= 2.00: count=0  mass=0
```

The `fineRatio` statistic is more structural:

```text
moderate_fineRatio >= 0.50: count=149 mass=2.157597
moderate_fineRatio >= 0.75: count=136 mass=1.865319
moderate_fineRatio >= 1.00: count=0
```

Across all coherent rows:

```text
ratio median=1.060599 max=1.893190
fineRatio median=0.852200 max=0.998427
```

Worst moderate rows:

```text
p=231169 M=1806 mass=0.246187 X128=24.39 X64=14.07
  fine128=10.32 fine64=3.43 ratio=1.734 fineRatio=0.734

p=288257 M=2252 mass=0.129143 X128=22.69 X64=11.99
  fine128=10.71 fine64=5.92 ratio=1.893 fineRatio=0.893

p=222337 M=1737 mass=0.088208 X128=20.13 X64=13.15
  fine128=12.75 fine64=7.36 ratio=1.530 fineRatio=0.969

p=158209 M=1236 mass=0.078733 X128=18.31 X64=11.30
  fine128=11.08 fine64=2.23 ratio=1.621 fineRatio=0.981
```

## Conclusion

The coarse ratio split is not enough: much of the moderate branch has
`X128/X64best` only around `1.1--1.4`.  The sharper invariant is that the new
fine gain is comparable to the ancestor magnitude:

```text
fine128 / X64best ≈ 0.75--1.00.
```

This is a near-doubling event under same-phase joining.  The next
theorem-shaped branch should be:

```text
large n=128 coherent path
  -> inherited high-fine/high-X64 ancestor,
  -> or moderate ancestor with near-doubling fine gain.
```

The second branch is not a pure tail event.  It should be attacked as a
pair-counting statement for same-phase child joins whose fine increment is
nearly the parent child's full magnitude.
