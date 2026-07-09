# #466 R263 n=64 child-phase alignment

## Hypothesis

R257--R262 show that the positive fine-layer route fails because isolated
`n=64` residual spikes survive trimming and become enormous after
exponentiation.  The next non-positive route is to move before exponentiation
and inspect the dyadic tower identity

```text
eta64[j] = eta32[j] + eta32[j + M],
```

where `p = 64*M + 1`.  A large positive fine residual should then be a
two-child coherence event: either both children are large and phase-aligned, or
one child is tiny and the other dominates.

## Probe

```bash
python3 scripts/probes/probe_r263_n64_child_phase_alignment.py \
  --min-index 512 --max-index 12000 --chunk 8192 \
  --top-per-row 4 --min-fine 8 --sort fine --top 25

python3 scripts/probes/probe_r263_n64_child_phase_alignment.py \
  --min-index 512 --max-index 12000 --chunk 8192 \
  --top-per-row 4 --min-fine 10 --sort fine --top 12
```

The probe computes raw complex periods, forms the two children
`a = eta32[j]`, `b = eta32[j+M]`, and records

```text
phase_cos = Re(a * conj(b)) / (|a| |b|)
pair      = sqrt(childA * childB) * max(phase_cos, 0).
```

## Result

For `R >= 8`, among the top four fine spikes for every prime row in
`512 <= M <= 12000`:

```text
spikes=3595
max_fine=20.21264456
min_phase_cos=-1.00000000
median_phase_cos=1.00000000
phase_cos_ge_0.9=3592/3595
```

The three exceptions are not high-MGF rows; they have one essentially zero
child and one large child:

```text
M=9429  p=603457 fine=8.464691 childA=0.010810 childB=17.817004 cos=-1
M=9430  p=603521 fine=8.075424 childA=0.000039 childB=16.200419 cos=-1
M=10558 p=675713 fine=8.660444 childA=0.000533 childB=17.513852 cos=-1
```

For the genuinely dangerous layer `R >= 10`, the obstruction becomes perfectly
clean:

```text
spikes=727
max_fine=20.21264456
min_phase_cos=1.00000000
median_phase_cos=1.00000000
phase_cos_ge_0.9=727/727
```

The worst rows are all coherent two-child events:

```text
M=10404 p=665857 fine=20.2126 X64=33.219 lift32=13.007 childB=20.651 cos=1.0000
M=10900 p=697601 fine=18.6895 X64=34.059 lift32=15.370 childB=18.773 cos=1.0000
M=9163  p=586433 fine=16.3004 X64=25.740 lift32=9.440  childB=16.829 cos=1.0000
M=10900 p=697601 fine=16.1459 X64=28.851 lift32=12.705 childB=16.254 cos=1.0000
```

## Conclusion

The R257--R262 survivors are not random positive-tail mass.  Above the useful
threshold they are exactly dyadic child-coherence events in the identity
`eta64 = eta32_left + eta32_right`.

This redirects the proof search.  A viable repair should target a signed
tower-cocycle large-deviation statement: no path can repeatedly select
large-magnitude, same-phase children often enough to beat the `sqrt(2)` L2
growth.  Positive layer-cake bounds have already lost the sign before the
decisive event appears.

Existing Lean substrate already isolates this gap:

* `SubgroupGaussSumTowerL2.secondMoment_tower_pow` proves exact L2 doubling.
* `SubgroupGaussSumTowerL2.maxNorm_tower_le_pow` records the trivial Linf
  doubling.
* `Frontier._R31LagSpectrumWeilBound.lag_correlation_bound` controls pair-lag
  correlations under a standard two-character Weil input; the remaining
  obstruction should be phrased as a higher-order coherence/cocycle bound.
