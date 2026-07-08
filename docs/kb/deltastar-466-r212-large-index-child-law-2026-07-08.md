# δ* #466 — R212 large-index child law

R212 names the remaining child concentration target:

```text
LargeIndexNormalizedChildLaw s t Θ δ Bbulk Bspike Mper
```

This bundles the R189/R193/R203 child-side requirements:

- nonnegative staircase increments;
- staircase domination of `exp(t/4)`;
- bulk-plus-two tail law;
- normalized bulk budget;
- normalized spike/staircase-mass budget;
- split-budget fit `Bbulk + Bspike <= 2`.

The theorem

```text
prize_sq_of_raw_dyadic_prizeTower_child_laws
```

composes R210 with two such child laws.  The route is now extremely explicit:
to move beyond consumers, prove `LargeIndexNormalizedChildLaw` for the actual
large-index dyadic Gauss-period child spectra on the `2^128` prize tower.
