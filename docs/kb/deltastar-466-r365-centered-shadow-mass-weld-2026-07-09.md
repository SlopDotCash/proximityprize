# Issue #466 R365: centered shadow-mass weld

Date: 2026-07-09

## Correction and result

The raw `KernelShellCensus` introduced in R362 cannot hold at deep prize moments: an index-`q`
lattice has a uniform population of approximately `1/q` of the ambient shell. R365 defines

```text
centeredShadowMass
  = q * (shadowEnergy + shadowCollisionMass) - n^(2r)
```

and proves that, for the exact-order power-root subgroup, this is exactly

```text
q * rEnergy(G,r) - |G|^(2r).
```

Consequently `DCEnergyBound G r` is equivalent to the corresponding centered-shadow-mass Wick
bound. Both statements are axiom-clean.

## Remaining target

The deep relation-lattice theorem must control the weighted discrepancy of short kernel shells
from their uniform `1/q` population. Raw shell cardinality is the right producer only for the
shallow rungs before the DC crossover. This correction aligns the R314–R362 relation machinery
with the prize's mandatory DC subtraction and prevents the random kernel population from being
mistaken for anomalous collision mass.
