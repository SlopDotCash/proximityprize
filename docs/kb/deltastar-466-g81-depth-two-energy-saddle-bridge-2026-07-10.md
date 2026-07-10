# G81: depth-two energy-to-saddle bridge

Date: 2026-07-10  
Issue: #466  
Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G81DepthTwoEnergySaddleBridge.lean`

## Result

G79S absorbs a primitive depth-two sector once its orbit-representative count `J` satisfies
`J*r^2 <= n^2`. G81 proves the weaker square-root-energy criterion

```text
J^2 <= C^2*n^3,    C^2*r^4 <= n  ==>  J*r^2 <= n^2.
```

It also proves the standard energy interface

```text
n*J <= E,    E^2 <= C^2*n^5  ==>  J^2 <= C^2*n^3,
```

and composes both inequalities with G79S's padded-sector consumer.

At the nominal production point `n=2^30`, `r=110`, the arithmetic accepts `C=2`, since
`4*110^4 <= 2^30`. Thus a full primitive depth-two energy estimate
`E <= 2*n^(5/2)` (in the cleared square form) is sufficient to absorb the sector. This is
strictly weaker than the linear-orbit assumption in G79S's first concrete corollary.

## Honest residual

This does not prove the energy estimate or the canonical orbit-to-energy injection. The next
load-bearing step is to connect G80's maximal-cancellation encoding to the actual depth-two
additive energy and prove `n*J <= E`. After that, one needs an explicit-constant subgroup energy
bound strong enough for `C=2` at the production cell. No Paley/sup-norm estimate is assumed by
the G81 arithmetic itself.

## Verification

`scripts/pg-iterate.sh` passes. Headline declarations use only the standard axioms reported by
their imported finite combinatorics (`propext`, `Classical.choice`, `Quot.sound`); the
energy-cancellation lemma itself reports only `propext`.
