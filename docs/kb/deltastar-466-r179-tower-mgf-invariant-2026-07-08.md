# δ* #466 — dyadic tower MGF invariant (2026-07-08)

## Hypothesis

R177 identified the marginal dyadic law as approximately `χ²_1`.  R178 then
showed the distribution is nearly invariant under the dyadic refinement
`μ_n ⊂ μ_{2n}` at a fixed prime.  R179 asks whether the R168 finite-grid/MGF
certificate itself is a tower invariant:

```text
I(μ_n) ≤ 2  =>  I(μ_{2n}) ≤ 2,
```

where `I` is either the R168 MGF

```text
M^{-1} Σ_C exp(X_C / 8)
```

or the `0.5`-grid staircase certificate.

Probe: `scripts/probes/probe_r179_tower_mgf_invariant.py`.

## Result

Interactive same-field tower (`p=100609`):

```text
tower prime p=100609
n    cosets    mgf       grid0.5   low<0.5  S1       S4       maxX
----------------------------------------------------------------------------------
8    12576     1.149302  1.193451  0.4986   0.3375   0.0440   7.772
16   6288      1.151827  1.196378  0.5121   0.3262   0.0423   11.343   dMGF=+0.002525
32   3144      1.152981  1.197135  0.5153   0.3133   0.0455   11.917   dMGF=+0.001153
64   1572      1.167459  1.212617  0.5477   0.2875   0.0452   19.391   dMGF=+0.014479
128  786       1.158128  1.203400  0.5344   0.2901   0.0458   11.737   dMGF=-0.009331
```

With `max_order=256` in the same field:

```text
256  393       1.156668  1.201661  0.5445   0.3053   0.0509   9.117    dMGF=-0.001459
```

The MGF and grid certificate stay in a narrow band:

```text
MGF      ≈ 1.15..1.17
grid0.5  ≈ 1.19..1.21
```

far below the R168 budget `2`.

## Verdict

The concentration route now has a sharper structural target than a raw
survival theorem:

```text
Prove a dyadic-tower bin-budget invariant.
```

At the proof level, the period decomposition is

```text
η_{2n}(C) = η_n(C_0) + η_n(C_1),
```

where `C_0,C_1` are the two child cosets.  R178 measured a stable cancellation
profile for this split; R179 shows the downstream R168 MGF certificate is also
stable along the same tower.  The Lean-facing endpoint already exists as
`dyadicTailMGF_of_bin_budget` in `_R168DyadicTailEnvelopeConsumer.lean`.

Honest scope: this is not yet a proof of the prize.  It gives a plausible
inductive invariant for the dyadic tail route.  The remaining mathematical
content is to prove that the two-child split preserves the bin budget, i.e. to
replace the observed cancellation/polarization profile by a deterministic
inequality.
