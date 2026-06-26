# Issue #464: slack-profile floor contract

Date: 2026-06-26.

Status: **contract bridge**, not a delta-star proof.

## Thesis

The exact profile/fiber route required a finite representative family to contain a true global
bad-scalar maximizer.  The slack-profile route is slightly different: a representative does not have
to be the exact maximizer of its fiber if every stack in the fiber is within an advertised slack
allowance and the representative-plus-slack budget is small enough.

This pass adds the floor-facing bridge:

```text
floor-good at |F|
+ floor-good -> used profile representatives plus slack are within B
+ every stack is below rep(profile u) plus slack(profile u)
=> WorstCaseIncidenceBounded
=> delta-star lower pin
```

The new Lean file is:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackFloorBridge.lean
```

## New Sockets

The missing floor-to-count theorem is named directly:

```lean
FloorGoodProfileSlackBudget
```

It says that once the deployed field is good for the modeled floor predicate, the profile slack
budget follows:

```text
not FloorBad (2^a) |F|
  -> ProfileFiberSlackBudgeted F C delta profile rep slack B.
```

The field-level certificate is:

```lean
ProfileSlackClosureAtField
profileSlackClosureAtField_of_floorGoodProfileSlackBudget
worstCaseIncidenceBounded_of_profileSlackClosureAtField
deltaStar_pin_of_profileSlackClosureAtField
```

The Linnik/TZ-facing consumers are:

```lean
profileFiberSlackBudgeted_of_linnik_candidateListExactSmallest
worstCaseIncidenceBounded_of_linnik_candidateListExactSmallest_profileSlackContract
deltaStar_pin_of_linnik_candidateListExactSmallest_profileSlackContract
profileFiberSlackBudgeted_of_tz_candidateListExactSmallest
worstCaseIncidenceBounded_of_tz_candidateListExactSmallest_profileSlackContract
deltaStar_pin_of_tz_candidateListExactSmallest_profileSlackContract
```

These theorems do not prove the least-prime or TZ inputs.  They only state the exact way those
inputs could feed a slack-profile budget if the missing floor-to-count theorem is supplied.

## Refutation Surface

The new exact failure form is:

```lean
not_profileSlackClosureAtField_iff_bad_or_stack_exceeds_slack_or_usedProfile_budget_lt
```

So a proposed slack-floor closure fails in exactly one of three ways:

```text
1. the modeled floor predicate is still bad at |F|;
2. some stack exceeds rep(profile u) + slack(profile u);
3. some used profile has rep p + slack p above B.
```

The floor-good-to-slack-budget theorem itself has its own scanner form:

```lean
not_floorGoodProfileSlackBudget_iff_floorGood_and_exists_usedProfile_budget_lt
```

That is the critical no-laundering guardrail.  If floor-goodness is true but a used profile's
representative-plus-slack allowance is above budget, then the proposed off-BGK floor theorem has
failed exactly there.

## Critique Of The Route

This bridge is useful because it avoids an artificial exact-max requirement.  A future analytic
profile theorem might plausibly prove same-profile stability with slack even when exact fiber
maximizers are too brittle.

But it does not evade the #464 wall by itself.  The slack domination theorem is still a universal
statement over every stack:

```text
forall u, StackBadCount u <= StackBadCount (rep (profile u)) + slack(profile u).
```

If the profile is too coarse, the previous constant-profile endpoint says this becomes a global
pairwise diameter theorem.  If the profile is too fine, the identity/injective endpoint says the
budget is just the original all-stack incidence problem.  A useful proof must therefore find an
intermediate compressed profile and prove genuine fiber oscillation control.

## Literature/PDF Inventory Note

The local ArkLib PDF inventory currently contains 327 PDFs under `/Users/shawwalters/papers/arklib`.
The exact Thorner-Zaman `2108.10878` PDF was not found by filename search in that corpus in this
pass; the Lean route continues to treat the TZ supply as a named hypothesis, not as an extracted
proved theorem.

## Next Attack

The next non-tautological target is a profile construction with:

```text
compression:     profile is neither constant nor injective;
oscillation:     same-profile bad-scalar counts differ by <= slack p;
budget:          floor-goodness, not direct enumeration, budgets rep p + slack p.
```

Absent such a construction, the slack route is only a clean API around the already known BGK/Paley
core.
