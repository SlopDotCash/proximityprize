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

G80R refuted G79S's raw padding envelope. G81 repairs it arithmetically by paying the missing
padding factorial from the unused Wick head. G82 composes its energy criterion with that corrected
full-Wick consumer.

At the nominal production point `n=2^30`, `r=110`, the arithmetic accepts `C=2`, since
`4*110^4 <= 2^30`. Thus a full primitive depth-two energy estimate
`E <= 2*n^(5/2)` (in the cleared square form) is sufficient to absorb a sector satisfying G81's
factorial-corrected envelope. This is strictly weaker than a linear-orbit assumption.

The sharp version keeps the exact insertion factor `(r descFactorial 2)^2` and exact two-factor
Wick tail `(2r-1)(2r-3)` instead of bounding them separately by `r^4` and `r^2`. The resulting
condition is

```text
C^2 * (r descFactorial 2)^4 <= oddWickTail(r,2)^2 * n.
```

At `(2^30,110)` this accepts `C=10` (with about 17% squared slack). The theorem
`production_corrected_depth_two_energy_absorbed_sharp` kernel-checks the full corrected envelope
from `E^2 <= 100*n^5`. This factor-five constant improvement is important because the remaining
analytic input is an explicit-constant subgroup additive-energy estimate.

## Honest residual

This does not prove the energy estimate or the canonical orbit-to-energy injection. The next
load-bearing step is to construct the factorial-corrected maximal-cancellation encoding, connect
its primitive count to the actual depth-two additive energy, and prove `n*J <= E`. After that,
one needs an explicit-constant subgroup energy
bound strong enough for `C=2` at the production cell. No Paley/sup-norm estimate is assumed by
the G82 arithmetic itself.

## Verification

`scripts/pg-iterate.sh` passes. Headline declarations report only `propext`.
