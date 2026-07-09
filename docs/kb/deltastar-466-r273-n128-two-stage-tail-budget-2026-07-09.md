# #466 R273 n=128 two-stage tail budget

## Question

R272 refuted a one-piece top-tail certificate because inherited resonance rows
pollute the top-tail mass.  This probe applies the intended two-stage split:

```text
1. inherited if selected n=64 ancestor has large fine64 or large X64;
2. on the remaining moderate rows, apply top-rank/tail-value/fine-ratio filters.
```

## Command

```bash
python3 scripts/probes/probe_r273_n128_two_stage_tail_budget.py \
  --min-index 512 --max-index 6000 --chunk 4096 \
  --top-per-row 4 --min-fine128 10 --top 20
```

## Result

Total mass over scanned high-fine rows:

```text
rows=233
total_mass=3.24657199
```

Baseline split `fine64 < 8`, `X64 < 16` leaves:

```text
inherited mass = 1.088975
moderate mass  = 2.157597
```

Across the tested inherited thresholds, the smallest top-tail subbranch found
inside the moderate bucket used

```text
topRank <= 4, tailX >= 2, fineRatio >= 0.95.
```

But this only makes the certified subbranch small by leaving major moderate
rows uncovered:

```text
fineCut xCut inheritedMass moderateMass bestTailMass
6       14   2.230433      1.016138     0.119897
8       16   1.088975      2.157597     0.208105
10      18   0.742789      2.503783     0.208105
```

Worst baseline moderate rows:

```text
p=231169 M=1806 mass=0.246187 X128=24.39 fine128=10.32
  X64max=14.07 fine64=3.43 bestRank=1 worstRank=4 fineRatio=0.734

p=288257 M=2252 mass=0.129143 X128=22.69 fine128=10.71
  X64max=11.99 fine64=5.92 bestRank=1 worstRank=4 fineRatio=0.893

p=222337 M=1737 mass=0.088208 X128=20.13 fine128=12.75
  X64max=13.15 fine64=7.36 bestRank=1 worstRank=20 fineRatio=0.969
```

## Conclusion

The naive two-stage certificate is still incomplete.  The inherited split is
necessary, but a strict top-tail certificate such as `fineRatio >= 0.95` misses
the largest moderate row:

```text
p=231169, fineRatio=0.734, mass=0.246187.
```

So the next residual is not just "moderate top-tail with near-full fine gain."
It includes a lower-fineRatio moderate branch where the parent value is large
because the ancestor is already moderately large and the opposite child is also
large, even though the fine increment is only about `0.73 * X64`.

The proof search should now split the moderate branch by fineRatio:

```text
moderate high-fineRatio branch: top-tail certificate may work;
moderate low-fineRatio branch: needs a separate two-large-child/top-top-ish
certificate, starting with p=231169.
```
