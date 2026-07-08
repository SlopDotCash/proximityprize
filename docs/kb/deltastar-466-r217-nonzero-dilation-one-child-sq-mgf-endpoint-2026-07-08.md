# δ* #466 — R217 nonzero dilation one-child square-MGF endpoint

R217 corrects the direct square-MGF endpoint onto the nonprincipal carrier.
The full frequency set contains `b = 0`, where the Gauss period is the DC term
`η_G(0) = |G|`; that is not the prize-facing concentration target.

The theorem composes:

```text
NonzeroNormalizedSqQuarterMGFResidual ψ G σ
```

from R213 with the one-child permutation consumer from R215.  Multiplication by
`ζ ≠ 0` preserves

```text
nonzeroFreqs = univ.erase 0,
```

so the shifted child `b ↦ ‖η_G(ζ*b)‖² / σ²` is a permuted copy of the unshifted
child on the nonzero carrier.  Together with `eta_union_dilate_norm_le`, this
gives the R168/S11 squared prize bound for the concrete normalized dilation
parent

```text
b ↦ ‖η_{G ∪ ζG}(b)‖² / (2σ²)
```

assuming the standard moment bridge.

Verified command:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R217NonzeroDilationOneChildSqMGFEndpoint.lean
```

Output:

```text
'ArkLib.ProximityGap.Frontier.R217NonzeroDilationOneChildSqMGFEndpoint.mulLeftPerm_mem_nonzeroFreqs' depends on axioms: [propext,
'ArkLib.ProximityGap.Frontier.R217NonzeroDilationOneChildSqMGFEndpoint.largeIndexChildQuarterMGF_of_nonzeroNormalizedSqResidual' depends on axioms: [propext,
'ArkLib.ProximityGap.Frontier.R217NonzeroDilationOneChildSqMGFEndpoint.prize_sq_of_nonzero_dilation_one_child_sqMGFResidual' depends on axioms: [propext,
OK (25s) — ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R217NonzeroDilationOneChildSqMGFEndpoint.lean
```

Readout: the structural residual from R215 is discharged on the correct
nonprincipal spectrum.  The remaining analytic wall is now precisely the R213
one-child nonzero normalized-square quarter-MGF residual.
