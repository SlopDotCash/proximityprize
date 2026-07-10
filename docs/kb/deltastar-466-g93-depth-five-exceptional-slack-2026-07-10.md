# G93 retraction: quotient-envelope arithmetic is not a raw-sector decoder

Lean artifact:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G93DepthFiveExceptionalSlackWeld.lean`.

G93 originally interpreted the generic scaling-orbit allowance

```text
generic <= n^8 / (28800 * 10).
```

and the exceptional `n^3` allowance as raw decoder core counts. That interpretation is retracted.
The concurrent G83 red-team found the missing coordinate: reconstructing an actual core from its
scaling-orbit representative also requires its scale in the subgroup, restoring a factor `n`.

The Lean arithmetic remains correct. At `(n,r)=(2^30,110)` it proves that the following
*conditional quotient envelopes* fit jointly inside one Wick budget:

- the certified depth-0 through depth-4 envelopes;
- the generic factor-ten quotient allowance;
- an additional `n^3` exceptional depth-five allowance.

It also proves that factor nine fails inside that same quotient model. Neither theorem supplies a
surjective decoder for actual endpoint mass, so neither is a production depth-five result.

The honest finite-depth frontier is G84's canonical-slot decoder with actual core-energy counts.
The orbit count `n^8 / 288000` is not by itself a sufficient target. Growing depths and production
`DCEnergyBound` remain open.

`scripts/pg-iterate.sh` passes. The three declarations use only `propext`; no `sorryAx`.
