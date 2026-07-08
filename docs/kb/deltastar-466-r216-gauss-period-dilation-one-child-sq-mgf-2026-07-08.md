# δ* #466 — R216 Gauss-period dilation one-child square MGF

R215 gave the abstract one-child direct-MGF consumer under a permutation of the
two normalized-square child spectra.  R216 instantiates the structural
permutation for the actual Gauss-period dilation recursion.

For nonzero `ζ`, the children are:

```text
rawLeft  b = ‖η_G(b)‖
rawRight b = ‖η_G(ζ * b)‖
```

Multiplication by `ζ` is a permutation of the full frequency set, so the right
normalized-square child spectrum is exactly the left spectrum after reindexing.
Together with `eta_union_dilate_norm_le`, R216 proves that the single input

```text
LargeIndexChildQuarterMGFLaw univ (fun b => ‖η_G(b)‖) σ
```

implies the R168/S11 squared prize bound for the concrete dilation parent
`‖η_{G ∪ ζG}(b)‖`, assuming the standard moment bridge.

Verified command:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R216GaussPeriodDilationOneChildSqMGF.lean
```

Output:

```text
'ArkLib.ProximityGap.Frontier.R216GaussPeriodDilationOneChildSqMGF.prize_sq_of_gaussPeriod_dilation_one_child_sqMGF' depends on axioms: [propext,
OK (12s) — ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R216GaussPeriodDilationOneChildSqMGF.lean
```

Readout: the structural half of the R215 residual is discharged for the full
frequency Gauss-period dilation model.  The remaining load-bearing analytic
statement is the one-child large-index square-normalized quarter-MGF law.
