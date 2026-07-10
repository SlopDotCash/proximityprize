# G87: the depth-five residual is exactly tenfold

Lean artifact:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G87DepthFiveTenfoldTarget.lean`.

The corrected-padding/free-orbit chain leaves the crude depth-five production universe

```text
n^8 * correctedPadEnvelope n 110 1 5,   n = 2^30.
```

Granting the largest evident coordinate symmetry contributes
`2 * (5!)^2 = 28800`: independent permutations of the two ordered five-coordinate cores and
side swap. G87 proves the exact integral cutoff

```text
depthFiveUniverse <= 28800 * c * fullWick  <->  10 <= c.
```

Thus factor nine is provably insufficient and factor ten is sufficient. This is sharper than
merely observing that G83's unsymmetrized overcount exceeds Wick.

## Honest boundary

The order-28800 action is not free on repeated-coordinate cores, so G87 grants more symmetry than
is automatically available. It neither supplies the extra factor ten nor proves the actual
primitive depth-five sector has the crude-universe cardinality. The positive target is now exact:
stratify stabilizers and obtain a total sector count at most `1/10` of the fully symmetry-reduced
crude universe, or replace the `n^8` ambient count by an estimate with the same saving.

`scripts/pg-iterate.sh` passes. All four declarations use only `propext`; there is no `sorryAx`.
Production `DCEnergyBound` and the exact δ* pin remain open.
