# G102: depth zero is the deterministic positive anomaly floor

Lean artifact:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G102DepthZeroAnomalyFloor.lean`.

G101 expresses `DCEnergyBound` as a signed sum over maximal-cancellation depths. G102 pins the
fully cancelled term.

Cancellation depth zero forces both residual cores to be empty. The two reconstruction identities
then show that both endpoint value multisets equal the same common multiset. Hence their additive
sums agree automatically, and

```text
depthFiber G r 0 = allPairsDepthFiber G r 0.
```

Therefore

```text
actualDepthAnomaly G r 0
  = (#F - 1) * allPairsDepthFiber G r 0
  >= 0.
```

The `s=0` contribution is thus the unavoidable diagonal/Wick floor; it never supplies negative
mass to compensate other depths. All genuinely signed cross-depth cancellation in G101 must occur
among depths `s >= 1`.

This is a sign localization, not an analytic bound on the residual depths. `scripts/pg-iterate.sh`
passes. All five declarations use only accepted foundational axioms; no `sorryAx`.
