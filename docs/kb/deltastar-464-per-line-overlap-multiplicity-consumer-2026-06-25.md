# Issue #464: per-line overlap multiplicity is the missing union-count consumer

Date: 2026-06-25.

Status: positive finite tool, not a delta-star proof.

## Claim refined

The previous per-line union gate showed the obstruction:

```text
if every active line has at most S bad scalars,
then the only automatic bound is #union <= #lines * S.
```

The June 25 issue comments sharpen the remaining obligation: a successful union-count route needs
real overlap/collapse. This note records the exact finite theorem that consumes such an overlap
input.

## Lean artifact

New Frontier file:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PerLineOverlapMultiplicityConsumer.lean
```

Definitions:

```lean
lineHitMultiplicity I lineBad x
```

counts how many active line fibers contain scalar `x`, and

```lean
lineIncidencePairs I lineBad
```

is the finite incidence set of pairs `(line, scalar)`.

The core double-count is:

```lean
sum_lineHitMultiplicity_eq_sum_card
```

which says that counting incidence pairs by scalar gives the same total as counting them by line:

```text
sum_{x in union} hitMultiplicity(x) = sum_{i in I} #(lineBad i).
```

The consumer is:

```lean
card_mul_le_sum_card_of_each_union_point_hit_many
```

If every scalar in the union is hit by at least `M` active lines, then

```text
#union * M <= sum_i #(lineBad i).
```

Combining with a per-line bound gives:

```lean
card_lineBadUnion_le_card_mul_div_of_each_le_and_overlap
```

namely

```text
#union <= (#lines * S) / M.
```

## Consequence for the floor route

This is the honest replacement for a false union-bound shortcut. The per-line count route can close
a prize-sized budget only if it proves one of the following:

1. `M` is comparable to `#lines`, so the line-count factor cancels.
2. The number of active lines is already budget-sized after the per-line bound.
3. A domination/classification theorem reduces the active-line family before taking the union.

The automatic theorem is only:

```lean
one_le_lineHitMultiplicity_of_mem_lineBadUnion
```

Every scalar in the union is hit at least once. This recovers the raw union bound and gives no
saving. Any `M > 1` is real new structure.

## What new math would look like

For the actual proximity-gap stack problem, the missing theorem should have the form:

```text
for every bad scalar gamma in the active union,
gamma is explained by at least M independent line/profile fibers.
```

or an equivalent orbit-collapse statement forcing many line fibers to coalesce on the same scalar.
At the finite bookkeeping layer, that would immediately deflate the union bound by `M`.

This does not touch the BGK/Paley core by itself. It only makes the overlap route precise: the next
mathematical work is to prove a nontrivial lower bound on `lineHitMultiplicity` for the actual active
families, not just for a toy incidence model.
