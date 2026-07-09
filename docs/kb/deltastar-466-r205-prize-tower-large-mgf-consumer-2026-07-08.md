# δ* #466 — R205 prize-tower large-MGF consumer

R205 combines:

- R203: the large-index normalized-budget quarter-MGF consumer;
- R204: the arithmetic fact that every child of the `2^128` prize quotient
  tower has index at least `1024`.

The theorem

```text
quarterMGF_of_prizeTowerIndex_threeFifths_plus_two_normalizedBudgets
```

says that if

```text
|s| = 2^128 * 2^depth
```

then the R189 normalized bulk/tail/spike hypotheses imply

```text
DyadicQuarterMGFBound s t.
```

This removes the medium-index distraction from the final prize route.  The
remaining non-bookkeeping mathematical targets are now the actual large-index
tail and normalized spike-mass estimates for the dyadic Gauss-period spectra
on the prize tower.
