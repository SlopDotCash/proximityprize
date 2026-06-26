# Issue #464: profile/cap route for stack domination

Date: 2026-06-25.

Status: **constructive interface**, not a delta-star proof.

## What This Adds

The finite-family max guardrail says a binder/floor catalogue must dominate all stacks.  The new
question is how such a domination theorem could be produced without guessing the global maximizer.

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_StackProfileDominationInterface.lean
```

formalizes a profile/cap route:

```lean
profile : WordStack A (Fin 2) iota -> P
cap : P -> Nat
```

The intended theorem shape is:

```text
StackBadCount(u) <= cap(profile(u))
```

for every stack `u`.

## Two Honest Consumers

The direct route is:

```text
ProfileCaps
+ every cap(p) <= B
=> WorstCaseIncidenceBounded C delta B
=> delta-star pin
```

This is the cleanest possible classification proof: each profile carries a certified worst-case
count, and all profile counts fit the budget.

The representative route is:

```text
ProfileCaps
+ every used profile cap is realized by some representative r in R
+ every r in R is bounded by B
=> WorstCaseIncidenceBounded C delta B
=> delta-star pin
```

This is the formal version of a binder/floor catalogue proof.  The catalogue must not merely contain
nice examples; it must realize the numerical caps assigned to all used stack profiles.

## Refutation Tests

The file also records exact ways to kill a proposed profile scheme:

```lean
not_familyBounded_iff_exists_member_budget_lt
not_profileCaps_iff_exists_counterexample
not_profileBudgeted_iff_exists_counterprofile
not_profileRealizedByFamily_iff_exists_counterprofile
not_profileRealizedByReps_iff_exists_counterprofile
not_profileCaps_and_profileBudgeted_iff_exists_counterexample_or_counterprofile
not_profileCaps_and_profileRealizedByFamily_and_familyBounded_iff_exists_counterexample_or_counterprofile_or_member_budget_lt
not_profileCaps_and_profileRealizedByReps_and_familyBounded_iff_exists_counterexample_or_counterprofile_or_member_budget_lt
```

These say respectively: a family budget fails by an above-budget representative; the profile cap
theorem fails by a stack above its assigned cap; the direct profile budget fails by a profile whose
cap exceeds `B`; and representative realization fails by a used profile whose cap is larger than
every representative's bad-scalar count.

The combined forms package the full certificate failures as scanner-facing alternatives.  The
direct profile route fails exactly by either a stack above its profile cap or a profile cap above
budget.  The representative route fails exactly by one of:

```text
1. a stack above its assigned profile cap;
2. a used profile whose cap is not reached by the proposed representatives;
3. an above-budget representative.
```

## Critical Verdict

This is the most concrete positive shape for the floor-localization route so far.

It does not say which profile space `P` is correct.  It says what the missing theorem must prove if
`P` is an adjacent-pattern, binder-type, monomial, orbit, or floor-localization profile:

```text
the profile cap is a true upper bound for all stacks in that profile,
and the resulting caps are either directly budgeted or realized by bounded representatives.
```

This prevents a common failure mode: proving that one convenient stack of a profile is small, then
treating that as a bound for the whole profile.  The required inequality goes the other way: every
stack in the profile must be no worse than the profile cap.
