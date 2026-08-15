# G101: exact signed-depth weld to DCEnergyBound

Lean artifact:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G101ExactSignedDepthWeld.lean`.

G96 decomposes the prize moment by maximal-cancellation depth and provides a sufficient consumer
using nonnegative depth caps. G100 proves those caps can lose cancellation between depths. G101
connects the lossless signed formulation to the actual depth fibers.

For a finite field `F`, alphabet `G`, moment depth `r`, and cancellation depth `s`, define

```text
actualDepthAnomaly_s =
  #F * depthFiber(G,r,s) - allPairsDepthFiber(G,r,s) : Z.
```

G101 proves exactly

```text
sum_s actualDepthAnomaly_s = #F * rEnergy(G,r) - #G^(2r)
```

and the equivalence

```text
DCEnergyBound G r
  <->
sum_s actualDepthAnomaly_s <= #F * (2r-1)!! * #G^r.
```

This is the lossless depth formulation. Negative anomalies at under-populated depths remain
available to cancel positive anomalies elsewhere; no positive-part operation or equal budget split
is introduced.

The theorem is connective rather than analytic: proving the signed-sum bound at production depth
is still the BGK/Paley wall. `scripts/pg-iterate.sh` passes. All three declarations use only
accepted foundational axioms; no `sorryAx`.

During verification, G95's locked build exposed a missing direct import of
`ArkLib.ToMathlib.Combinatorics.Additive.HigherEnergy`. Adding it makes the G95→G96 build chain
reproducible from a clean module environment.
