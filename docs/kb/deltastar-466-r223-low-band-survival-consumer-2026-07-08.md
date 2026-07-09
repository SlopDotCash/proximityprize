# δ* #466 — R223 low-band survival consumer

R222 repaired the false zero-bin tail by paying `θ = 0` exactly.  The next
failure was the first positive grid threshold.  R223 tests and formalizes a
slightly wider split:

```text
B(θ) = M                                      for θ <= τ
B(θ) = C * M * exp(-θ/2) + K                 for θ > τ
```

## Probe

Artifact:

```text
scripts/probes/probe_r223_low_band_split_budget.py
```

Prize-style run:

```text
python3 scripts/probes/probe_r223_low_band_split_budget.py \
  --mode prize --ns 64 128 256 512 --samples 20000 --seed 466223 \
  --steps 0.5 0.25 0.125 --taus 0 0.125 0.25 0.5 0.75 1 \
  --cutoff 32 --c-bulk 0.6 --scale 2 --spike-budget 2 --carrier coset
```

Readout:

```text
viable_rows=27
best_viable budget=1.698415 slack=0.301585 tailRatio=0.975011
step=0.125 tau=0.5
```

The prize random run also reports large rare-spike ratios for sampled extreme
points.  Those are not reliable evidence against a `+2` coset-carrier spike
reserve: one sampled hit has mass `1/20000`, while the actual coset-carrier
reserve is `2/M`.  Exact spectra are the authoritative check for the spike
term.

Exact-anchor run:

```text
python3 scripts/probes/probe_r223_low_band_split_budget.py \
  --mode exact --max-n 256 --max-p 350000000 \
  --steps 0.5 0.25 0.125 --taus 0 0.125 0.25 0.5 0.75 1 \
  --cutoff 32 --c-bulk 0.6 --scale 2 --spike-budget 2 --carrier coset
```

Readout:

```text
viable_rows=26
best_viable budget=1.701347 slack=0.298653 tailRatio=0.980030
n=128 p=268437889 step=0.125 tau=0.5
```

Small-index rows remain budget-dead; this is consistent with R217/R222 and
keeps the large-index branch separate from finite direct handling.

## Lean

Artifact:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R223LowBandSurvivalConsumer.lean
```

Main declarations:

```text
lowBandBulkSpikesBound
lowBandGridTail_of_above_tail
nonzeroNormalizedSqQuarterMGFResidual_of_lowBand_bulkPlusSpikes_tail
nonzeroNormalizedSqQuarterMGFResidual_of_lowBand_threeFifths_plus_two_tail
```

The theorem consumes only an above-band tail (`τ < θ`) and pays every
threshold `θ <= τ` by the full nonzero-frequency carrier.

## Conclusion

The near-zero obstruction from R222 is local: paying a low band through
`τ = 0.5` exactly leaves roughly `0.30` R213 MGF-budget slack on the exact
large-index anchors while making the `0.6 exp(-θ/2)+2` tail viable above the
band.

This sharpens the next analytic target:

```text
For large-index dyadic μ_n, prove
#{b : X_b >= θ} <= 0.6 * M * exp(-θ/2) + 2
only for θ > 1/2,
```

with the low band paid by the finite-grid certificate rather than by the
exponential envelope.
