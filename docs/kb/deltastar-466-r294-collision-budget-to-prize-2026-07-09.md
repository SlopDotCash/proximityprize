# #466 R294: collision-budget route to the prize socket

Date: 2026-07-09

## What landed

`Frontier/_R294CollisionBudgetToPrizeSocket.lean` connects the R293 scalar
collision-reduced sextic route back to the concrete R23/R287 interfaces.

The bridge names the two remaining identifications:

```text
CollisionProfileIdentifiesTripleConv P J
  := P.cubicEnergy = sum_d |tripleConv J d|^2

CollisionProfileUsesR23Scale q scale
  := scale = m^3 q^3
```

With those in hand, a scalar R293 cubic bound becomes the exact R23 rung-three
input:

```text
tripleConvEnergyBound_of_collisionReducedCubicScaleBound
tripleConvEnergyBound_of_collisionBudgetRoute
concreteRungThreeSubconvex_of_collisionBudgetRoute
```

The end-to-end consumer is:

```text
prizeFloor_of_collisionBudgetRoute_endpoint_upgrade_le_const
```

It composes:

```text
R293 CollisionBudgetRoute
  -> R23 TripleConvEnergyBound
  -> R287 ConcreteRungThreeSubconvex
  -> ConcreteDepthThreeToCeilUpgrade
  -> abstract DeepJacobiSubconvex / HyperplaneSubconvex / PrizeFloor socket
```

## What remains open

This is bookkeeping, not the prize proof.  The analytic work is now sharply
localized to:

1. proving the R293 generic-distinct signed sextic budget,
2. proving the repeated-index collision budget,
3. proving the two identifications above for the concrete Jacobi profile, and
4. supplying the genuine depth-three-to-ceiling upgrade without the R95/R96
   linear-in-`m` recurrence budget.

The file passed:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R294CollisionBudgetToPrizeSocket.lean
```
