# δ* #466 — R224 half-band tail consumer

R223 made the low-band split configurable.  R224 calibrates the coefficient
landscape for the above-band theorem:

```text
#{b : X_b >= θ} <= C * M * exp(-θ/2) + 2,   θ > τ.
```

## Probe

Artifact:

```text
scripts/probes/probe_r224_above_band_tail_constant.py
```

Exact-anchor run:

```text
python3 scripts/probes/probe_r224_above_band_tail_constant.py \
  --mode exact --max-n 256 --max-p 350000000 \
  --step 0.125 --taus 0 0.25 0.5 0.75 1 1.5 2 \
  --scales 1.5 2 2.5 3 --cutoff 32 --spike-budget 2 --carrier coset
```

Readout:

```text
global_required_C scale=2 C=0.772579 tau=0 theta=0.125
```

But after paying the low band through `τ = 1/2`, the worst large-index exact
rows require only:

```text
n=64:  C@2 = 0.5892 at θ=0.625
n=128: C@2 = 0.5880 at θ=0.625
n=256: C@2 = 0.5896 at θ=0.625
```

So the literal `C = 3/5` target is not supported for all positive thresholds,
but it is supported above the half-band in the tested large-index rows.

Prize sample run, using sample carrier to avoid mistaking one sampled rare hit
for coset-level mass:

```text
python3 scripts/probes/probe_r224_above_band_tail_constant.py \
  --mode prize --ns 64 128 256 512 --samples 30000 --seed 466224 \
  --step 0.125 --taus 0 0.25 0.5 0.75 1 1.5 2 \
  --scales 1.5 2 2.5 3 --cutoff 32 --spike-budget 2 --carrier sample
```

For scale `2` and `τ = 1/2`, required `C` is again about `0.59`.

## Lean

Artifact:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R224HalfBandTailConsumer.lean
```

Main declarations:

```text
halfBandThreeFifthsPlusTwoBound
nonzeroNormalizedSqQuarterMGFResidual_of_halfBand_threeFifths_plus_two_tail
```

This fixes the next clean analytic input:

```text
∀ θ ∈ Θ, 1/2 < θ →
  #{b != 0 : θ <= |η(b)|^2 / σ^2}
    <= (3/5) * M * exp(-θ/2) + 2.
```

The finite-grid proof then pays `θ <= 1/2` by the full carrier and consumes
that above-half tail to land the R213 quarter-MGF residual.

## Conclusion

The corrected normalized-square route has a sharper target than R217:

1. small indices remain a separate finite/direct branch;
2. large-index MGF budget survives if the grid pays `θ <= 1/2` exactly;
3. the remaining analytic claim is a half-band survival theorem with constants
   `(C, scale, K) = (3/5, 2, 2)` above `θ = 1/2`.

This is still an open distributional theorem, not a prize closure, but it is a
more precise conjecture to attack than the false all-positive `0.6` envelope.
