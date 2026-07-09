# δ* #466 — R201 small-direct / large-normalized consumer

R201 combines two landed interfaces:

- R197: split the quarter-MGF residual into finite `M < 32` direct
  certificates and a large-index branch;
- R193: express the large-index branch with normalized bulk and per-point
  spike-mass budgets.

The Lean file is:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R201SmallDirectLargeNormalizedBudgets.lean
```

For the live R189 constants, the final theorem says:

```text
s.card < 32  -> direct DyadicQuarterMGFBound
32 <= s.card -> BulkPlusSpikesGridTail s t Θ (3/5) 2
32 <= s.card -> NormalizedBulkWeightedBudget Θ δ (3/5) <= Bbulk
32 <= s.card -> StaircaseMass Θ δ <= Mper * |s|
2 * Mper <= Bspike
Bbulk + Bspike <= 2
----------------------------------------------------------
DyadicQuarterMGFBound s t
```

This is deliberately narrow: it does not prove the analytic large-index
hypotheses, but it removes the previous weighted-budget bookkeeping from the
main route.  The remaining mathematical targets are now exactly the ones the
R196/R200 probes are testing:

1. finite small-index direct certificates;
2. large-index bulk-plus-two tail;
3. large-index normalized spike mass / logarithmic max control.
