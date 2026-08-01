# G313: all-rank coefficient-2 positivity at certified toy scale

Date: 2026-08-01
Issue: #466
Branch: `research/proximity-prize`

## Result

G300 shows that the coefficient-2 adjacent-rank CORE covariance can oscillate inside the small
window: for `mu_8 <= F_113^*`, the exact sequence is

```text
A_r = [392, 128, -7240, -13128, -13128, -7240, 128].
```

G297 shows that the coefficient-1 dilation anchor does not reliably transport to the coefficient-2
target on the small cell `mu_16 <= F_113^*`:

```text
r=5: A1=-2977296, A2=+1727120
r=6: A1= +152176, A2=  -77440
```

G313 checks the same exact adjacent-rank object at certified mission-scale field size. Proth theorem
certifies

```text
p = 111*2^128 + 1
```

prime with witness `5`. For `n=16`, the probe computes every adjacent rank `r=1..15` by sparse
subset histograms and weighted-kernel dot products. It also direct-enumerates the subset pairs for
the live ranks `r=5,6` as an independent cross-check.

At this field scale:

```text
coefficient 1: dot=0 at every rank, so A1 = -256*C(16,r)*C(16,r-1) < 0
coefficient 2: dot values are
  [16, 576, 8064, 64064, 321216, 1064448, 2369472, 3544608,
   3544608, 2369472, 1064448, 321216, 64064, 8064, 576],
  so A2 > 0 at every rank r=1..15.
```

The coefficient-2 row also satisfies the expected reflection palindrome on `r=2..15`.

## Scope

This is a finite scale audit, not a production theorem. It uses `n=16`, not `n=2^30`, and it proves
no logarithmic-depth or worst-case-over-frequency bound. The useful content is narrower: the
small-cell sign pathologies do not persist uniformly under this `n=16` large-field audit, and at the
certified Proth-prime scale the coefficient-2 target is positive on the entire adjacent-rank window
checked.

## Artifact

- Probe: `scripts/probes/g313_all_rank_window_scale_audit.py`
- Output: platform temp directory `arklib-reports/g313_all_rank_window_scale_audit.out`
