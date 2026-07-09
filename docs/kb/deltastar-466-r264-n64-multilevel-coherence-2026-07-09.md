# #466 R264 n=64 multilevel coherence

## Question

R263 showed that dangerous `n=64` fine residuals are child-phase alignment
events in

```text
eta64[j] = eta32[j] + eta32[j + M],      p = 64*M + 1.
```

This note tests the stronger hypothesis: are these spikes late-stage accidents,
or do they follow persistent same-sign/coherent ancestry through the dyadic
tower

```text
8 -> 16 -> 32 -> 64?
```

For each high `n=64` fine spike, the probe selects the larger child at each
descent and records the child-pair phase cosines for the joins
`32 -> 64`, `16 -> 32`, and `8 -> 16`.

## Probe

```bash
python3 scripts/probes/probe_r264_n64_multilevel_coherence.py \
  --min-index 512 --max-index 12000 --chunk 8192 \
  --top-per-row 4 --min-fine 10 --sort fine64 --top 12
```

The scan recomputes raw complex periods at `n = 8, 16, 32, 64`, then traces the
ancestor branch of every top-four `n=64` fine spike with `R >= 10`.

## Result

The full R263 dangerous set is persistently coherent:

```text
rows=727
max_fine64=20.21264456
cos64_ge_0.9=727/727
cos32_ge_0.9=727/727
cos16_ge_0.9=727/727
all_three_ge_0.9=727/727
median_min_path_cos=1.00000000
min_min_path_cos=1.00000000
```

Worst rows:

```text
M=10404 p=665857 fine64=20.2126 X64=33.219
  X32 children = 13.01, 20.65; best32=20.65 best16=10.33 best8=7.80
  cos64=1.000 cos32=1.000 cos16=1.000

M=10900 p=697601 fine64=18.6895 X64=34.059
  X32 children = 15.37, 18.77; best32=18.77 best16=11.39 best8=6.26
  cos64=1.000 cos32=1.000 cos16=1.000

M=9163 p=586433 fine64=16.3004 X64=25.740
  X32 children = 9.44, 16.83; best32=16.83 best16=8.79 best8=6.51
  cos64=1.000 cos32=1.000 cos16=1.000
```

## Interpretation

The tempting "single late coherent join" repair is refuted for the dangerous
`R >= 10` set.  The high `n=64` residuals are supported on persistent coherent
branches all the way down to `n=8`.

This makes the next proof target sharper:

```text
count or exponentially tax dyadic tower paths whose child joins are
simultaneously same-sign and large at many consecutive levels.
```

In Lean terms, this should sit between the two already formalized facts:

* `SubgroupGaussSumTowerL2.secondMoment_tower_pow`: exact L2 doubling.
* `SubgroupGaussSumTowerL2.maxNorm_tower_le_pow`: trivial Linf doubling.

The missing theorem is a signed/cocycle large-deviation statement forcing the
Linf behavior to track the L2 growth except on a small, explicitly taxable set
of persistent coherent branches.  Pair-lag control alone is unlikely to close
this, because the obstruction is now visibly a multilevel path event.
