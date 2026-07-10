# Rate-quarter integral K5 barrier and global four-line cap (2026-07-10)

## Result

At the P1 immediate predecessor

```text
N = 2^30 = 1073741824
K = 2^28 = 268435456
T = 592794966,
```

integer multiplicity counting is strictly stronger than the divided Plotkin
bound.  For five subsets, `5s <= s^2+6` gives

```text
20 z <= 6 N + 20 lambda.
```

At `z=T` and `lambda=K-1`, the inequality is violated by `44739276`.
Consequently every five predecessor agreement sets contain a pair whose
intersection has at least `K` coordinates.  In graph language, the complement
of the large-overlap graph is `K5`-free, so its independence number is at most
four.  Exact four-part Turan then forces asymptotically one quarter of all
scalar pairs to have `K`-large secant cores; at `|G|=N+1` the lower bound is

```text
144115187807420416
```

unordered large-core pairs.

The same inequality applies to distinct polynomial-line cores because the
ordinary degree-`<K` root bound gives pair intersections at most `K-1`.  The
exact integral onset is

```text
FourLineCoreFloor = floor((6N+20(K-1))/20)+1 = 590558003.
```

Thus at most four distinct degree-`<K` polynomial lines can have cores at or
above `590558003`.  This is `2236961` coordinates below the near-saturated
size `T-2`, so in particular it is an unconditional global four-line cap for
all near-saturated and saturation-violating pencils.  No primitive-factor or
collapsed-cluster hypothesis is required.

Fresh-fibre packing sharpens the operational form: a relevant line carrying
at least `216` selected explanations must reach `FourLineCoreFloor`, hence at
most four relevant lines carry `216` or more points.  At core `590558002`,
`215` points still fit; `216` exceed the universe by `402`.

The formal statements are in
`Frontier/_P1RateQuarterAgreementOverlapGraph.lean`:

```text
fiveSet_integral_johnson
exists_pair_inter_card_ge_K_of_five
largeOverlapGraph_compl_cliqueFree_five
turan_fourPart_lower_bound_largeOverlap_edges
no_five_nearSaturated_lines
coreFloor_lines_card_le_four
nearSaturated_lines_card_le_four
lines_with_216_points_card_le_four
```

All were checked by `scripts/pg-iterate.sh` with no `sorryAx`.

## Stability increment

The six-set inequality `7s <= s^2+12` also yields an exceptional-pair
amplifier.  If fourteen of the fifteen intersections are at most `K-1`, the
last is at least

```text
Z1 = 18T - 6N - 14(K-1) = 469762074.
```

For globally trimmed `T`-sets, two `Z1` attachments to one center intersect
on more than `K` coordinates and therefore have the same polynomial secant
direction.  This is formalized in
`Frontier/_P1RateQuarterExceptionalPairAmplification.lean`.

## Honest remaining gap

This does not yet prove the predecessor bad-count bound.  The unresolved
case is a potentially huge supply of lower-core lines carrying at most `215`
points each (two-point lines are the extreme obstruction).  Pair-partition
mass alone permits that channel.  The next proof must inject algebraic
dependence between those many secants, or show that an over-budget family is
absorbed by the at-most-four `590558003`-core lines.  The global count-four
part of the former four-pencil residual is now unconditional; extraction of
the lower-core remainder is the live part.
