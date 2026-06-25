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

The file also records two ways to kill a proposed profile scheme:

```text
1. find u with cap(profile(u)) < StackBadCount(u);
2. find a used profile p such that every r in R has StackBadCount(r) < cap(p).
```

The first refutes the cap theorem.  The second refutes the representative realization theorem.

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
