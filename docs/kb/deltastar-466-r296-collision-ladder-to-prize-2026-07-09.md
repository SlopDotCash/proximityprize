# #466 R296: collision ladder to the prize socket

Date: 2026-07-09

## What landed

`Frontier/_R296CollisionLadderToPrizeSocket.lean` adapts the existing R295
three-part repeated-index collision ladder into the R293 collision-budget route,
then feeds that route through the R294/R287 prize-floor consumer.

The adapter defines:

```text
reducedProfileOfCollisionLadder P r q
CollisionLadderUsesClosedWick P r q
```

The first views an R295 `CollisionLadderProfile` as the R293
`CollisionReducedProfile`.  The second records the necessary closed-Wick
identification:

```text
P.wickPerfectClosed = wickBucketClosed r q.
```

The main consumers are:

```text
collisionReducedDecomposition_of_collisionLadderDecomposition
collisionBudgetRoute_of_collisionLadderBudgets
prizeFloor_of_collisionLadder_endpoint_upgrade_le_const
```

## Route

The end-to-end path is now:

```text
R295 generic + mixed + 21x21 + cube collision budgets
  -> R293 CollisionBudgetRoute
  -> R23 TripleConvEnergyBound
  -> R287 ConcreteRungThreeSubconvex
  -> ConcreteDepthThreeToCeilUpgrade
  -> abstract PrizeFloor socket.
```

## Remaining analytic load

This is still not the prize proof.  The adapter leaves the real work explicit:

1. prove the generic-distinct-with-Wick bound,
2. prove the mixed distinct/two-one collision budget,
3. prove the two-one/two-one budget,
4. prove the cube-involving cleanup budget,
5. identify the scalar profile with the concrete Jacobi triple-convolution
   energy and R23 scale,
6. prove the depth-three-to-ceiling upgrade without the R95/R96 linear
   `m <= 4*C` recurrence budget.

## Validation

The relevant checks passed:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R295MixedCollisionLadderSocket.lean
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R296CollisionLadderToPrizeSocket.lean
```
