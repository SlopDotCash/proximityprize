# R222: zero-split survival consumer

Date: 2026-07-08

Artifact:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R222ZeroSplitSurvivalConsumer.lean`

## Result

R222 packages the corrected survival-grid socket after the zero-threshold
obstruction.

The previous literal bulk-plus-spikes envelope

```text
(3/5) * carrier * exp(-θ/2) + 2
```

cannot honestly cover the `θ = 0` count, because at zero threshold the survivor
set is the full nonzero-frequency carrier.  The corrected envelope is
zero-split:

```text
if θ = 0 then carrier
else Cbulk * carrier * exp(-θ/2) + Kspike
```

The Lean file proves:

- `zeroSplitGridTail_of_positive_tail`: a positive-threshold tail extends to a
  valid grid tail by paying the full carrier at zero.
- `nonzeroNormalizedSqQuarterMGFResidual_of_zeroSplit_bulkPlusSpikes_tail`: the
  zero-split grid tail feeds the R213 normalized-square quarter-MGF residual.
- `nonzeroNormalizedSqQuarterMGFResidual_of_zeroSplit_threeFifths_plus_two_tail`:
  the literal `(3/5, 2)` specialization, now guarded by the zero split.

## Probe Evidence

The companion probe used in this lane was:

```text
scripts/probes/probe_r222_zero_split_grid_budget.py
```

Prize-style run:

```bash
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

```bash
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

## Verification

Fast lane:

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R222ZeroSplitSurvivalConsumer.lean
```

Status: passed.

## Prize status

This is a correctness guard for the survival-tail route.  It does not prove the
positive-threshold analytic tail; it prevents future consumers from smuggling in
the false `θ = 0` instance of that tail.

The live analytic obstruction has moved to the first positive thresholds.  With
`C = 0.6`, the empirical tail ratio is about `1.28` near `θ = 0.125`, so the
next target should either pay an initial low-threshold band exactly or prove a
stronger low-threshold law with bulk coefficient close to `1` near zero and
decaying toward `0.6` after the initial band.
