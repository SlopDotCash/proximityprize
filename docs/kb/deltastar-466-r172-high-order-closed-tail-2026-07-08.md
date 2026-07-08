# δ* #466 — high-order stress for closed-form grid tail (2026-07-08)

## Hypothesis

R170 proposed the closed-form grid survival law

```text
N(T) ≤ (3/4) M exp(-T/4),      T ∈ 0.5·ℕ, T ≥ 1.
```

R172 tests whether this is just a low-order artifact by moving to larger
dyadic orders where exact coset spectra remain feasible.

Probe: `scripts/probes/probe_r172_high_order_closed_tail.py`.

## Result

```text
n    p          cosets    maxX     tail_ratio T     count   grid0.5 mgf
----------------------------------------------------------------------------------------
256  65537      256       10.732   0.541698   1     81      1.19900 1.15624
256  67073      262       8.138    0.548896   1     84      1.19847 1.15229
256  70657      276       11.625   0.589287   1     95      1.19970 1.15486
256  70913      277       8.231    0.556256   1     90      1.20241 1.15552
256  75521      295       9.464    0.551333   1     95      1.19734 1.15299
256  16777729   65538     16.587   0.545940   1     20899   1.19882 1.15438
256  16778497   65541     19.085   0.544530   1     20846   1.19883 1.15447
256  16780289   65548     17.291   0.543088   1     20793   1.19879 1.15443
256  16780801   65550     18.164   0.545579   1     20889   1.19887 1.15435
512  262657     513       16.168   0.553991   1     166     1.20071 1.15709
512  265729     519       12.436   0.540990   1     164     1.20149 1.15643
512  270337     528       13.513   0.544738   1     168     1.19911 1.15605
512  275969     539       10.044   0.546326   1     172     1.19702 1.15227

summary
worst_tail ratio=0.589287 n=256 p=70657 T=1.0 count=95
worst_grid ratio=1.202414 n=256 p=70913
tail_violations=0
```

## Verdict

The closed-form grid tail law survives the larger-order stress pass.  The
worst ratio again occurs at the bulk threshold `T=1`, not in the high tail.
The finite-grid MGF certificate remains stable around `1.20`, well below the
R168 target `2`.

This supports the current proof target:

```text
Prove a dyadic bulk-and-tail survival theorem on the half-integer grid:
  #{C : |η_C|²/σ² ≥ T} ≤ (3/4) M exp(-T/4).
```

The hard part now appears to be the bulk concentration near `T=1`, while the
exceptional high-tail cosets are safely within the same envelope at these
larger orders.
