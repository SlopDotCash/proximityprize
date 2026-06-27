# Issue #464: arbitrary ratio profiles obstruct support-only caps

Date: 2026-06-26.

Status: **structural obstruction**, not a delta-star floor proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Lean Surface

File:

```text
ArkLib/Data/CodingTheory/ProximityGap/RatioCensusWeightIdentity.lean
```

This pass adds:

```lean
ArkLib.ProximityGap.RatioCensus.ratioSeq_negProfile_one
ArkLib.ProximityGap.RatioCensus.ratioMult_negProfile_one
ArkLib.ProximityGap.RatioCensus.farIncidence_negProfile_one_eq_fiberLevel
ArkLib.ProximityGap.RatioCensus.not_uniform_ratioMult_cap_of_fiber_gt
```

## Content

The exact ratio-census identities do not impose a degree-like multiplicity cap by themselves.  For
any map

```text
r : iota -> F,
```

the full-support line

```text
s1(i) = 1,
s0(i) = -r(i)
```

has ratio sequence exactly `r`.  Therefore its ratio multiplicity at `gamma` is exactly the fibre
size

```text
#{i : r(i) = gamma}.
```

The weight-bad incidence is correspondingly exact:

```text
#{gamma : hammingWeight((-r) + gamma*1) <= w}
  = #{gamma : |iota| - w <= #{i : r(i) = gamma}}.
```

So if a profile has a fibre larger than `m`, the associated line refutes the uniform cap
`forall gamma, ratioMult gamma <= m`.

## Prize Impact

This is the obstruction behind the current ratio-degree route.  The structured polynomial-line
closure in `RatioMultiplicityBridge.badWeight_empty_of_degree_exact` is real progress, but it
depends on polynomial/low-degree structure.  It cannot be extended to arbitrary received-word
stacks by support-counting alone, because arbitrary stacks can encode arbitrary ratio profiles.

Any floor proof using this lane must therefore supply one of the missing global inputs:

```text
1. a domination/reduction theorem putting worst stacks inside bounded-degree polynomial lines, or
2. a separate codeword-pair/list-supply bound strong enough to sum the per-line incidence layer.
```

## Validation

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/RatioCensusWeightIdentity.lean
```

The new theorem audit lines report only the standard Lean axioms:
`propext`, `Classical.choice`, and `Quot.sound`.
