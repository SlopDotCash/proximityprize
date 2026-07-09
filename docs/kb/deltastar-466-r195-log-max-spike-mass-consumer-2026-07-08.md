# #466 R195: log-max spike-mass consumer

Status: deterministic consumer, not a proof of the finite-field max bound.

R194 tested the scalar spike side of the bulk/spike quarter-MGF route. The exact case-set run found:

```text
worst_defect = maxX - 4 log M = -5.435433
worst_ratio  = exp(maxX/4)/M = 0.256954
violations maxX <= 4 log M - 5: 0
```

The crude R191 spike-ratio target was `0.199786`; only two tiny quotient sizes violated it:

```text
M = 16, ratio = 0.256954
M = 21, ratio = 0.209646
```

For `M >= 32`, the worst ratio dropped to `0.145620`, already inside the crude target. At prize
scale the spike ratio is far below budget.

## Lean consumer

`_R195LogMaxSpikeMassConsumer.lean` proves the deterministic bridge:

```text
StaircaseMass <= exp(Xmax/4)
Kspike * exp(Xmax/4) <= Bspike * M
------------------------------------
Kspike * StaircaseMass <= Bspike * M
```

and a logarithmic version:

```text
Xmax <= 4 log (Bspike*M/Kspike)
--------------------------------
Kspike * StaircaseMass <= Bspike*M
```

assuming the log argument and `Kspike` are positive.

## Resulting proof target

The spike side is no longer the main blocker. A viable proof can split:

1. certify the finite tiny quotient cases (`M = 16, 21`, and whatever exact finite list the final
   constants require);
2. prove a large-index logarithmic max-period bound, empirically as strong as
   `maxX <= 4 log M - 5`;
3. combine with the R193 covariance/mean slack consumer to close the product-MGF budget `<= 2`.

This is still open mathematics, but it is a sharply reduced target: a coarse extreme-value bound
plus a very slack covariance bound, not exact Gaussian domination.
