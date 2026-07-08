# δ* #466 — R171 closed-form grid-tail consumer (2026-07-08)

## Purpose

R170 identified a proof-friendly empirical survival law:

```text
N(θ) ≤ (3/4) M exp(-θ/4)
```

on the `0.5`-spaced grid.  R171 wires that law into the existing R168/S11 Lean
consumer.

## Lean Update

Updated:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R168DyadicTailEnvelopeConsumer.lean
```

New pieces:

```text
DyadicClosedFormGridTail
dyadicTailMGF_of_closedFormGridTail
```

The theorem says: if the closed-form tail bound holds on the chosen finite
threshold grid, and the corresponding weighted closed-form envelope is at most
`2 |s|`, then the concrete R168 MGF residual follows.

## Remaining Mathematical Target

The route is now factored cleanly:

1. Prove the dyadic survival-count theorem
   `#{b : θ ≤ t_b} ≤ (3/4)|s| exp(-θ/4)` on the grid.
2. Prove the pure numerical weighted-sum inequality for the grid.
3. Consume R168/S11 to get the moment envelope, energy-transfer slack, and
   prize-square bound.

Verified:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R168DyadicTailEnvelopeConsumer.lean
```
