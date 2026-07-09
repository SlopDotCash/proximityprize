# δ* #466 — R207 prize-tower step consumer

R207 combines:

- R205: a prize-tower child spectrum with R189 normalized bulk/spike budgets
  has `DyadicQuarterMGFBound`;
- R188: two child quarter-MGF bounds plus the dyadic parent pointwise
  inequality imply the parent `DyadicTailMGFBound`.

The theorem is:

```text
dyadicTailMGF_of_prizeTower_child_normalizedBudgets
```

It is the current one-step prize-tower proof shape.  The remaining mathematical
content is no longer bookkeeping:

1. prove the dyadic parent pointwise inequality for the actual Gauss-period
   parent/children;
2. prove the R189 normalized large-index tail and spike-mass budgets for both
   children in the `2^128 * 2^depth` quotient-index regime.

R206 gives random-sampling stress evidence for (2) directly at the huge prize
index, but R207 is only a consumer until those analytic hypotheses are proved.
