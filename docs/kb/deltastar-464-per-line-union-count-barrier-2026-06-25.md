# Issue #464: per-line counts do not prove the union-count floor

Date: 2026-06-25.

Status: **union-count guardrail**, not a delta-star proof.

## Inputs Checked

- Live issue #464, especially the reduction of the floor to a worst-case bad-scalar count.
- `_ThreadD_UnionCountFloor.lean`, which proves that a uniform per-stack bad-scalar count within
  budget closes the `epsMCA` floor.
- `_FloorClosureContract.lean` and `_FloorDominationInterface.lean`, which separate finite-family
  bounds from worst-case stack domination.
- Existing KB notes on stack coverage, family domination, and the budgeted tail-count gate.

## Claim Tested

One tempting shortcut is:

```text
prove each fixed line/target contributes at most S bad scalars;
take the union over lines;
conclude the union still has size at most S.
```

This is the exact proof slip that `_ThreadD_UnionCountFloor.lean` warns against.  The prize-facing
quantity is the realized bad-scalar union for a stack, not a single fixed line.

## Lean Result

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PerLineUnionCountBarrier.lean
```

defines

```lean
lineBadUnion (I : Finset ι) (lineBad : ι -> Finset γ) : Finset γ
```

and proves the only automatic conversion:

```lean
card_lineBadUnion_le_card_mul_of_each_le
```

If every line has at most `S` bad scalars, the union is bounded only by

```text
#lines * S.
```

The file also proves the sharp obstruction:

```lean
perLineBound_not_unionBound_countermodel
```

It builds disjoint tagged fibers.  Every line fiber has size at most `S`, but if there are at least
two lines and `S > 0`, the union has size strictly larger than `S`.

## Consequence for #464

The union-count floor cannot be discharged from a per-line count alone.  To reach a budget of size
`S` after taking a union over many lines, a proof must add one of the following real inputs:

- an overlap/collapse theorem showing the line fibers coalesce enough that the union loses the
  `#lines` factor;
- a domination/classification theorem showing only one effective line family matters for the
  worst-case stack; or
- a smaller per-line budget strong enough to survive multiplication by the number of active lines.

This is exactly the distinction between the proven per-fixed-line field-independent counts and the
open distinct-gamma growth law.  Per-line bounds are useful local information, but the prize floor
consumes a union count.

## What New Math Would Look Like

The missing theorem should not say merely:

```text
for every line L, #bad(L) <= S.
```

It must say something closer to:

```text
#(union over active lines bad(L)) <= S,
```

or it must prove a structural collapse such as pairwise heavy overlap, a single orbit at binding, or
a worst-case stack classification.  Without that added structure, the disjoint-fiber model is a
finite counterexample to the shortcut.
