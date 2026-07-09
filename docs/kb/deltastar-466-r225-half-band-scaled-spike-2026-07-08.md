# δ* #466 — R225 half-band scaled-spike correction

R224 calibrated the half-band tail shape:

```text
θ > 1/2 => survival <= (3/5) * M * exp(-θ/2) + 2.
```

But the literal `+2` is a quotient-carrier spike reserve.  On the raw nonzero
frequency carrier, quotient evidence lifts with coset multiplicity:

```text
raw spike reserve = 2 * |G|.
```

This is the same correction as R220/R223, now applied to the half-band route.

## Lean

Artifacts:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R225HalfBandScaledSpikeConsumer.lean
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R225HalfBandQuotientTailConsumer.lean
```

Main declarations:

```text
halfBandThreeFifthsPlusScaledTwoBound
nonzeroNormalizedSqQuarterMGFResidual_of_halfBand_threeFifths_plus_scaledTwo_tail
halfBandScaledTwoBound
nonzeroNormalizedSqHalfBandTail_scaledTwo_of_quotient
nonzeroNormalizedSqQuarterMGFResidual_of_quotient_halfBand_tail
```

The corrected raw-frequency target is:

```text
∀ θ ∈ Θ, 1/2 < θ →
  #{b != 0 : θ <= |η_G(b)|^2 / σ^2}
    <= (3/5) * #nonzeroFreqs * exp(-θ/2) + 2 * |G|.
```

Equivalently, a quotient-orbit tail with literal `+2`, together with the
raw-to-quotient counting lift, feeds this raw endpoint.

## Check

```text
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R225HalfBandScaledSpikeConsumer.lean
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R225HalfBandQuotientTailConsumer.lean
```

Both pass.

## Conclusion

The half-band route remains alive, but the honest statement is quotient-first:
prove the above-half survival law on quotient orbits with `+2`, then lift to raw
frequencies with spike reserve `+2*|G|`.  Literal raw `+2` should not be used
unless the carrier is already quotient-sized or `|G| = 1`.
