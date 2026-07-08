# δ* #466 — R214 direct child-MGF law

R212 names the live child residual as a staircase/tail certificate:

```text
LargeIndexNormalizedChildLaw s t Θ δ Bbulk Bspike Mper
```

That is one route to the needed child estimate, but the deterministic dyadic
consumer ultimately uses only:

```text
DyadicQuarterMGFBound s (fun b => rawChild b^2 / σ^2)
```

R214 records the direct residual:

```text
LargeIndexChildQuarterMGFLaw s rawChild σ
```

and proves that two such child laws, together with the raw dyadic triangle and
the existing moment bridge, imply the same R168/S11 squared prize bound.

Verified command:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R214DirectChildMGFLaw.lean
```

Output:

```text
'ArkLib.ProximityGap.Frontier.R214DirectChildMGFLaw.childQuarterMGF_of_largeIndexChildQuarterMGFLaw' depends on axioms: [propext,
'ArkLib.ProximityGap.Frontier.R214DirectChildMGFLaw.prize_sq_of_raw_dyadic_prizeTower_child_quarterMGF' depends on axioms: [propext,
OK (32s) — ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R214DirectChildMGFLaw.lean
```

Readout: the open analytic target can now be attacked directly as the
large-index quarter-MGF law suggested by R206/R213, without committing to the
R189 staircase certificate as the only path.
