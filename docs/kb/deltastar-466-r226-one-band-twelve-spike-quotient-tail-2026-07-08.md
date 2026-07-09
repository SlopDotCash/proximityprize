# R226: one-band twelve-spike quotient tail

Status: live replacement hypothesis for the corrected quotient-tail route.

## What failed

The R225 half-band quotient target

```text
#{q : theta <= X_q} <= (3/5) * |Q| * exp(-theta/2) + 2,  theta > 1/2
```

is false as a uniform finite-index statement.

Exact sweep command:

```bash
python3 scripts/probes/probe_r226_half_band_quotient_tail_sweep.py \
  --ns 16 32 64 --max-p 200000 --max-cosets 50000 --limit-per-n 20
```

Worst row:

```text
worst_C_required=0.72304231
n=64 p=4481 M=70 theta=0.52129210 count=41
```

A wider sweep from `p >= 65537` shows a second obstruction: more than two
high quotient spikes.

```bash
python3 scripts/probes/probe_r226_half_band_quotient_tail_sweep.py \
  --ns 16 32 64 128 --min-p 65537 --max-p 1000000 \
  --max-cosets 250000 --limit-per-n 40
```

Worst row:

```text
worst_C_required=3.78475357
n=64 p=65537 M=1024 theta=16.52490516 count=3
```

So `+2` quotient spikes cannot be the large-index tail interface unless a
separate argument removes those exceptional rows.

## Replacement target

The currently viable exact target is:

```text
#{q : theta <= X_q} <= (3/5) * |Q| * exp(-theta/2) + 12,  theta > 1.
```

The low band through `theta <= 1` is paid exactly.  The quotient-to-raw lift
then gives a raw spike reserve `12 * |G|`.

Exact sweep:

```bash
python3 scripts/probes/probe_r226_half_band_quotient_tail_sweep.py \
  --ns 16 32 64 128 256 --min-p 65537 --max-p 5000000 \
  --max-cosets 200000 --limit-per-n 80 --tau 1.0 --spike-budget 12
```

Result:

```text
tested=400 skipped_by_cosets=0
worst_C_required=0.57071374
slack=0.02928626
n=64 p=65537 M=1024 theta=7.94541801 count=23
target_passes=True
```

Known shared-prime anchor:

```bash
python3 scripts/probes/probe_r226_half_band_quotient_tail_sweep.py \
  --ns 64 256 --min-p 16778497 --max-p 16778497 \
  --max-cosets 300000 --tau 1.0 --spike-budget 12
```

Result:

```text
n=64  p=16778497 M=262164 C_required=0.52666962
n=256 p=16778497 M=65541  C_required=0.52413
```

## MGF budget warning

The replacement tail is not by itself a proof for all moderate indices.  The
Fermat row `n=64, p=65537, M=1024` has exact quarter-MGF about `3.2624`, so it
cannot satisfy the prize endpoint and must belong to a finite/small-index
exception branch.

For the larger anchors, the same weighted staircase budget is viable.  With
`tau=1`, `C=3/5`, `K=12`, cutoff at the observed max, and step `0.125`:

```text
M=65541  cutoff=19.085 budget=1.80904 slack=0.19096
M=262164 cutoff=27.584 budget=1.83807 slack=0.16193
```

Lean consumer:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R226OneBandTwelveSpikeQuotientConsumer.lean
```

It proves that the one-band/twelve-quotient-spike tail, plus the raw lift and
finite weighted staircase budget, feeds `NonzeroNormalizedSqQuarterMGFResidual`.
