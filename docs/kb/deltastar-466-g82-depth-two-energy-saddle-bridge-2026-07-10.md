# G82: depth-two energy-to-saddle bridge

Date: 2026-07-10
Issue: #466
Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G82DepthTwoEnergySaddleBridge.lean`

## Result

The factorial-corrected full-Wick consumer requires its primitive depth-two orbit count `J` to
satisfy `J*r^2 <= n^2`. G82 proves the weaker square-root-energy criterion

```text
J^2 <= C^2*n^3,    C^2*r^4 <= n  ==>  J*r^2 <= n^2.
```

It also proves the standard energy interface

```text
n*J <= E,    E^2 <= C^2*n^5  ==>  J^2 <= C^2*n^3,
```

The file deliberately stops at this orbit budget: G80R refuted G79S's raw padding envelope, while
G81 supplies the separate factorial-corrected full-Wick arithmetic.

At the nominal production point `n=2^30`, `r=110`, the arithmetic accepts `C=2`, since
`4*110^4 <= 2^30`. Thus a full primitive depth-two energy estimate
`E <= 2*n^(5/2)` (in the cleared square form) is sufficient for the corrected consumer's orbit
budget. This is strictly weaker than a linear-orbit assumption.

## Honest residual

This does not prove the energy estimate or the canonical orbit-to-energy injection. The next
load-bearing step is to construct the factorial-corrected maximal-cancellation encoding, connect
its primitive count to the actual depth-two additive energy, and prove `n*J <= E`. After that,
one needs an explicit-constant subgroup energy
bound strong enough for `C=2` at the production cell. No Paley/sup-norm estimate is assumed by
the G82 arithmetic itself.

## Verification

`scripts/pg-iterate.sh` passes. Headline declarations report only `propext`.
