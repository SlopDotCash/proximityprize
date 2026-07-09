# #466 R265 n=64 persistent-path tax

## Question

R264 found that every dangerous `n=64`, `R >= 10` top-four fine spike in the
large-index scan is coherent through the full dyadic ancestry

```text
8 -> 16 -> 32 -> 64.
```

This follow-up asks whether such paths form a usable taxable exception class.
For thresholds on the selected ancestor branch at levels `8`, `16`, and `32`,
the probe measures how many coherent branches are captured and how much positive
`n=64` MGF mass they carry.

## Commands

```bash
python3 scripts/probes/probe_r265_n64_persistent_path_tax.py \
  --min-index 512 --max-index 12000 --chunk 8192 \
  --top-per-row 4 --min-fine 10 \
  --t8 5 6 7 --t16 9 11 --t32 14 16 --top 20

python3 scripts/probes/probe_r265_n64_persistent_path_tax.py \
  --min-index 512 --max-index 12000 --chunk 8192 \
  --top-per-row 4 --min-fine 10 --max-exact-mgf 2.0 \
  --t8 5 6 7 --t16 9 11 --t32 14 16 --top 20
```

The script caches the R264 ancestry rows once, then sweeps threshold triples.

## Unfiltered result

Without finite-row filtering, a persistent-path tax is still expensive:

```text
t8=5 t16=9  t32=14: captured=147 worstCapturedMass=0.96231205 at M=3193
t8=7 t16=11 t32=16: captured=14  worstCapturedMass=0.12446999 at M=10900
```

The row `M=3193, p=204353` is already an exact-MGF offender:

```text
exactMGF=2.6321, capturedMass=0.96231205, one captured branch.
```

So the path event alone does not close the full problem; finite high-MGF rows
must be split off or certified separately.

## Filtered branch: exact MGF <= 2

After filtering to rows with exact `n=64` MGF at most `2`, the path tax becomes
much smaller:

```text
t8=5 t16=9  t32=14: captured=141 worstCapturedMass=0.06167858
t8=5 t16=9  t32=16: captured=58  worstCapturedMass=0.03524213
t8=6 t16=9  t32=14: captured=89  worstCapturedMass=0.03663029
t8=7 t16=11 t32=16: captured=13  worstCapturedMass=0.01375022
```

Worst filtered rows:

```text
M=11685 p=747841 capturedMass=0.06167858 captured=2 exactMGF=1.5099
M=6175  p=395201 capturedMass=0.03663029 captured=1 exactMGF=1.5323
M=7617  p=487489 capturedMass=0.03524213 captured=1 exactMGF=1.4308
M=1752  p=112129 capturedMass=0.02902104 captured=1 exactMGF=1.4109
M=6634  p=424577 capturedMass=0.01375022 captured=1 exactMGF=1.4191
```

## Conclusion

The persistent-path tax is not a standalone proof: unfiltered finite rows still
carry too much mass.  But it survives as a plausible branch after a finite
exception split.  In the exact-MGF `<= 2` branch, coherent path mass is small
enough to become a socket for a proof by:

1. finite certification of exact-MGF offender rows, plus
2. a structural bound on persistent coherent branches in the remaining rows.

The next attack should turn the threshold scan into a theorem-shaped statement:
an ancestor-threshold counting bound for paths with same-sign joins at
`8 -> 16 -> 32 -> 64`, then test whether it scales to `n=128`.
