# G90: adaptive depth budgets remove the artificial 111-fold loss

Lean artifact:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G90AdaptiveDepthBudgetAssembly.lean`.

G89's even split is a clean sufficient assembly rule, but it is not a necessary production
condition. Requiring every one of the 111 depths to fit one 111th of Wick artificially multiplies
the isolated depth-five target. In particular, the `1005` cutoff obtained by applying the equal
split to G87 must not be read as an intrinsic combinatorial barrier.

G90 proves a lossless replacement:

- `allDepth_le_fullWick_of_adaptiveBudgets`: arbitrary per-depth budgets suffice whenever their
  sum is at most the full Wick budget;
- `distinguishedDepth_le_fullWick_of_residual`: one live depth may consume the exact residual after
  all other depths are paid;
- `distinguishedDepth_le_fullWick_of_other_le`: the same rule with an aggregate certified bound
  for the non-live depths;
- `adaptive_of_evenSplit`: G89's equal-share condition implies the adaptive consumer, so no
  previous sufficient result is lost.

## Consequence

The production-facing depth-five calculation should be performed against

```text
fullWick - (certified mass of every other depth),
```

not against `fullWick / 111`. Since depths 0–4 have explicit bounds far below arbitrary equal
shares, their unused budget can be reassigned. The original factor-10 single-depth calibration is
therefore not automatically inflated to 1005; the exact adaptive cutoff awaits a simultaneous
bound for the remaining depths 6–110.

This repairs an assembly normalization issue, not CORE. The growing-depth caps remain the
BGK/Paley wall. `scripts/pg-iterate.sh` passes; all four declarations use only standard axioms and
contain no `sorryAx`.
