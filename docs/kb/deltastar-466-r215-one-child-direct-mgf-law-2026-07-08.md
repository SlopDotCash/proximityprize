# δ* #466 — R215 one-child direct MGF law

R214 reduced one raw dyadic prize-tower step to two direct child quarter-MGF
laws:

```text
LargeIndexChildQuarterMGFLaw s rawLeft σ
LargeIndexChildQuarterMGFLaw s rawRight σ
```

R215 proves the deterministic permutation reduction.  If the right child
normalized-square spectrum is the left child normalized-square spectrum after a
permutation preserving `s`,

```text
rawRight i ^ 2 / σ^2 = rawLeft (e i) ^ 2 / σ^2,
```

then the right child inherits the left child quarter-MGF law.  Consequently,
one child law plus this permutation datum is enough for the same R168/S11
squared prize bound.

Verified command:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R215OneChildDirectMGFLaw.lean
```

Output:

```text
'ArkLib.ProximityGap.Frontier.R215OneChildDirectMGFLaw.largeIndexChildQuarterMGF_of_perm' depends on axioms: [propext,
'ArkLib.ProximityGap.Frontier.R215OneChildDirectMGFLaw.prize_sq_of_raw_dyadic_prizeTower_one_child_quarterMGF' depends on axioms: [propext,
OK (16s) — ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R215OneChildDirectMGFLaw.lean
```

Readout: the dyadic-MGF route now has two sharp residuals:

1. prove the direct large-index child quarter-MGF law for one child spectrum;
2. prove the finite-field quotient/frequency permutation equality between the
   two normalized-square child spectra.

The second item is structural rather than analytic, and should be attacked in
the Gauss-period dilation/shift lanes next.
