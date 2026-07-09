# δ* #466 — small-direct / large-tail split consumer (2026-07-08)

## Hypothesis

R196 showed that tiny index cases should not be forced through the R189/R194
large-index spike route.  They are better handled by finite direct
`DyadicQuarterMGFBound` certificates, while the large range uses the
bulk-plus-spikes tail envelope.

## Lean artifact

File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R197SmallDirectLargeTailSplit.lean`.

Main theorem:

```text
s.card < N      -> direct DyadicQuarterMGFBound
N <= s.card     -> BulkPlusSpikesGridTail + weighted budget
----------------------------------------------------------
DyadicQuarterMGFBound
```

The live specialization sets `N = 32`, matching the R196 cutoff.

## Verification

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R197SmallDirectLargeTailSplit.lean
```

R197 passed the fast Lean check in 5 seconds.

## Verdict

The quarter-MGF proof can now be organized as:

1. `M < 32`: finite direct certificates;
2. `M >= 32`: R189/R190/R194 large-index tail route.

This cleanly removes the tiny-index exceptions from the asymptotic spike-mass
argument.
