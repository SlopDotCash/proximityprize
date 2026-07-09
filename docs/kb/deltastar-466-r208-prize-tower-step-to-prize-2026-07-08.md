# δ* #466 — R208 prize-tower step to prize bound

R208 composes the current prize-tower route:

```text
R207 child normalized budgets -> parent DyadicTailMGFBound
R168 parent DyadicTailMGFBound + moment bridge -> squared prize bound
```

The Lean theorem is:

```text
prize_sq_of_prizeTower_child_normalizedBudgets
```

It lands:

```text
Mmax^2 <= 2 * exp(1) * (2 / (1/8)) * n * r
```

from:

- `|s| = 2^128 * 2^depth`;
- dyadic parent pointwise control `parent_i <= left_i + right_i`;
- R189 normalized bulk/tail/spike hypotheses for both child spectra;
- the standard R168/S11 moment-to-sup bridge.

This is still a consumer, not the prize closure.  Its value is to make the
remaining proof obligations visible without medium-index clutter:

1. prove the actual dyadic parent normalization inequality;
2. prove the large-index R189 normalized budgets for child Gauss-period spectra
   in the prize tower;
3. connect the resulting square-root-log bound through the already documented
   incidence/δ* bridge.
