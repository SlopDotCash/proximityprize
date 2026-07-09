# R235: quotient residual-tail lift

Issue: #466. Date: 2026-07-08.

## Context

R234 already contains a raw nonzero-frequency split consumer:

```text
direct raw top payment + raw residual survival tail -> quarter-MGF residual
```

The successful probes are quotient-facing, so the missing deterministic bridge
is not another generic MGF split.  It is the residual quotient-to-raw lift:
after deleting the directly-paid raw top set, quotient residual survivors
should cover raw residual survivors with multiplicity at most `|G|`.

## Lean socket

New file:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R235QuotientResidualTailLift.lean
```

It introduces:

```text
residualOrbitCarrier G T
QuotientResidualGridTail Qres qSq Θ Bq
RawResidualTailLeCosetScale ψ G σ T Qres qSq Θ
```

and proves:

```text
ResidualNormalizedSqGridTail ψ G σ T Θ (fun θ => |G| * Bq θ)
```

from those two inputs.  It then composes with R234:

```text
nonzeroNormalizedSqQuarterMGFResidual_of_topRank_quotient_residual_tail
```

The direct top payment remains raw.  The residual tail may now be proved on a
quotient carrier and lifted into the raw R234 consumer.

The file also packages the natural Gauss-period residual lift:

```text
rawResidualTailLeCosetScale_of_gauss_residual_orbit_score
nonzeroNormalizedSqQuarterMGFResidual_of_topRank_natural_quotient_residual_tail
```

These specialize `Qres` to `residualOrbitCarrier G T`, assuming the residual
raw carrier is stable under multiplication by `G` and the quotient score
dominates raw residual survivors on their orbits.

## Verification status

The first R235 compile attempt failed before reaching the new code because the
local mathlib cache was missing an olean:

```text
Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.olean does not exist
```

After that, `pg-iterate` on both prerequisite consumers
`_R234RankSumResidualMGFConsumer.lean` and
`_R216NonzeroNormalizedSqSurvivalConsumer.lean` failed with existing
`Unknown constant Semiring.toMonoid` errors around normalized-square notation.
The locked repair build was also waiting behind another checkout build.

So the socket still needs `pg-iterate` once the cache/lock situation clears;
the current failure happens in existing imported files before R235-specific
obligations are checked.
