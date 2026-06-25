# Issue #464: the full floor-closure contract

Date: 2026-06-25.

Status: **closure-interface progress**, not a delta-star proof.

## What changed

I added:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorClosureContract.lean
```

This file connects three pieces that were previously documented separately:

```text
FloorLocalizationUniform + Linnik/TZ supply -> not FloorBad
not FloorBad -> finite family bounded
finite family dominates all stacks -> WorstCaseIncidenceBounded
```

The new predicate is:

```lean
FloorGoodFamilyBudget FloorBad a C delta R B
```

It means: once the prize prime is good for the modeled floor predicate, the chosen finite family
`R` of stacks is within the bad-scalar budget `B`.

## Consumers

The Linnik-form consumer is:

```lean
worstCaseIncidenceBounded_of_linnik_floorClosureContract
deltaStar_pin_of_linnik_floorClosureContract
```

The Thorner-Zaman-form consumer is:

```lean
worstCaseIncidenceBounded_of_tz_floorClosureContract
```

So even the sharpened TZ least-prime supply still does not close the prize by itself.  It supplies
only the floor-goodness input.  A complete proof still needs:

```text
FloorGoodFamilyBudget
FamilyDominates
```

These are exactly the algebra/incidence and sparse-domination bridges missing from issue #464.

## Scanner Refutation Hooks

The file also records two direct falsification tests:

```lean
floorGood_familyBudget_not_dominationProof_of_larger_than_all
floorGood_familyBudget_not_worstCaseIncidenceBounded_of_counterStack
```

An exact scanner can now attack the floor lane in two clean ways:

```text
find uWitness beating every r in R
```

which refutes `FamilyDominates`, or:

```text
find uWitness with StackBadCount(uWitness) > B
```

which refutes the universal incidence conclusion at budget `B`, even if floor-goodness bounded the
listed floor family.

## Critical Verdict

The off-BGK floor route now has a precise proof contract:

```text
smallest-prime localization
+ sub-4 least-prime supply
+ floor-good -> family budget
+ family domination
=> delta-star lower pin
```

The first two inputs are arithmetic.  The last two are the real coding-theoretic load.  If they
fail, the smallest-prime theorem remains obstruction removal for a modeled family, not a proof of
`WorstCaseIncidenceBounded`.

The next useful work is not another Linnik wrapper.  It is either:

```text
prove FloorGoodFamilyBudget for the adjacent-profile family,
prove FamilyDominates for that family,
or produce a scanner witness outside the family with larger bad-scalar count.
```

That is the sharpest current form of the floor gap.
