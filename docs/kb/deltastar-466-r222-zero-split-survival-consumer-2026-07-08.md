# δ* #466 — R222 zero-split survival consumer

R221 refuted the literal survival envelope at `θ = 0`.  R222 tests and
formalizes the corrected socket:

```text
B(0) = M
B(θ) = C * M * exp(-θ/2) + K       for θ ≠ 0
```

where `M` is the carrier size.

## Probe

Artifact:

```text
scripts/probes/probe_r222_zero_split_grid_budget.py
```

Prize-style run:

```text
python3 scripts/probes/probe_r222_zero_split_grid_budget.py \
  --mode prize --ns 64 128 256 512 --samples 20000 --seed 466222 \
  --steps 1 0.5 0.25 0.125 --cutoff 32 \
  --c-bulk 0.6 --scale 2 --spike-budget 2 --carrier coset
```

Readout:

```text
best_split_budget=1.631542 slack=0.368458 n=64 step=0.125
worst_positive_tail_ratio=1.287151 n=128 step=0.125 theta=0.125
```

Exact-anchor run:

```text
python3 scripts/probes/probe_r222_zero_split_grid_budget.py \
  --mode exact --max-n 256 --max-p 350000000 \
  --steps 1 0.5 0.25 0.125 --cutoff 32 \
  --c-bulk 0.6 --scale 2 --spike-budget 2 --carrier coset
```

Readout:

```text
best_split_budget=1.634474 slack=0.365526 n=128 p=268437889 step=0.125
worst_positive_tail_ratio=1.287628 n=64 p=16778497 step=0.125 theta=0.125
```

Small-index rows remain budget-dead with literal `K = 2`; they need the
separate finite/direct branch already indicated by R217.

## Lean

Artifact:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R222ZeroSplitSurvivalConsumer.lean
```

Main declarations:

```text
zeroSplitBulkSpikesBound
zeroSplitGridTail_of_positive_tail
nonzeroNormalizedSqQuarterMGFResidual_of_zeroSplit_bulkPlusSpikes_tail
nonzeroNormalizedSqQuarterMGFResidual_of_zeroSplit_threeFifths_plus_two_tail
```

The theorem shape is deliberately honest: it consumes only a positive-threshold
tail (`θ ≠ 0`) and pays the zero threshold by the full carrier.

## Conclusion

The R216/R213 finite-grid route survives the R221 correction.  The false
unsplit zero-bin hypothesis is replaced by a viable zero-split budget with
large-index slack around `0.36` on the tested grid.

The live analytic obstruction has moved to the first positive thresholds:
with `C = 0.6`, the empirical tail ratio is about `1.28` near `θ = 0.125`.
So the next hypothesis should not be "same exponential tail for every
positive θ"; it should either:

1. pay an initial low-threshold band exactly, then use the `0.6 exp(-θ/2)+K`
   bulk tail above a cutoff; or
2. prove a stronger low-threshold distributional law with bulk coefficient
   close to `1` near zero and decaying to `0.6` after the initial band.
