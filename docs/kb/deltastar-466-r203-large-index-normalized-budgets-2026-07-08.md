# δ* #466 — R203 large-index-only normalized consumer

R202 found a clean obstruction to a universal small/medium direct split:
some medium-index dyadic rows have `MGF(1/4) > 2`.  That does not directly
hit the prize row, because the prize tower has quotient index of order
`2^128` at the top and even larger quotient index in lower children.

R203 therefore removes the universal small-case fallback and exposes the
large-index interface directly:

```text
N <= |s|
BulkPlusSpikesGridTail s t Θ Cbulk Kspike
NormalizedBulkWeightedBudget Θ δ Cbulk <= Bbulk
StaircaseMass Θ δ <= Mper * |s|
Kspike * Mper <= Bspike
Bbulk + Bspike <= 2
----------------------------------------------------------
DyadicQuarterMGFBound s t
```

The live specialization is also provided with the R189 constants and
`N = 1024`:

```text
quarterMGF_of_large1024_threeFifths_plus_two_normalizedBudgets
```

This is still a consumer, not a proof of the analytic hypotheses.  Its value is
that the final prize route can now target the actual large-index regime rather
than false medium-index universality.
