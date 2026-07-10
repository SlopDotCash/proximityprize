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

## Stronger production overcount: energy is unnecessary at depth two

The full double factorial has much more slack than the factorwise G81/G82 comparison uses. The
entire universe of ordered depth-two core pairs has cardinality at most `n^4`, before imposing any
equal-sum, disjointness, primitivity, or rotation-orbit condition. G82 now kernel-checks

```text
(2^30)^4 * correctedPadEnvelope(2^30, 110, 1, 2)
  <= (2*110-1)!! * (2^30)^110.
```

Thus even assigning one complete factorial-corrected padding envelope to every ordered core pair
fits in the production Wick budget. Once the actual factorial-corrected decoder is constructed,
the whole depth-two sector can be absorbed by this crude universe bound; neither `n*J <= E` nor
an additive-energy estimate is needed for this depth.

This method stops sharply at depth three. The analogous unrestricted universe has `n^6` ordered
core pairs, and G82 proves the strict reverse production inequality: its corrected envelopes
exceed the full Wick budget by about `2^4.52`. This does not refute the actual equal-sum depth-three
sector; it shows exactly where genuine additive-energy/family-cancellation structure first becomes
necessary, matching the dossier's independently identified sextic core.

## Honest residual

This does not prove the factorial-corrected maximal-cancellation decoder. That decoder is now the
only remaining depth-two obligation. The energy bridge remains useful for other parameter cells,
but it is no longer load-bearing at the nominal production point. Higher primitive depths still
require collective control and are not discharged by the depth-two universe count.

## Verification

`scripts/pg-iterate.sh` passes. Headline declarations report only `propext`.
