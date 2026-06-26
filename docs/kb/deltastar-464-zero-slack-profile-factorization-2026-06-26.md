# Issue #464: zero-slack profile factorization

Date: 2026-06-26.

Status: **critical refinement**, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The previous profile work squeezed the slack route between two endpoints:

```text
constant profile  -> global pairwise bad-count diameter;
injective profile -> original all-stack incidence theorem.
```

The remaining possible middle case is a genuinely non-injective profile with small same-fiber
oscillation.  This pass isolates the zero-slack version of that middle case and removes a small
artifact of the previous formulation: the representative is not the invariant.  The invariant is
that bad-scalar counts are constant on each profile fiber.

The representative-free zero-slack condition is:

```text
profile u = profile v
  ->
StackBadCount u = StackBadCount v.
```

In Lean this is `ProfileBadCountFiberConstant`.

If representatives lie in their used fibers, zero same-profile oscillation is exactly:

```text
StackBadCount u = StackBadCount (rep (profile u))
```

for every stack `u`.  In other words, the bad-count must factor through the chosen profile
representative.  A compressed profile with zero slack is useful only if it merges distinct stacks
without changing their bad-scalar count.

## Lean Additions

In `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackDominance.lean`:

```lean
ProfileBadCountRepresented
ProfileBadCountFiberConstant
profileBadCountFiberConstant_of_zero_oscillation
profileFiberOscillationBounded_zero_of_profileBadCountFiberConstant
profileFiberOscillationBounded_zero_iff_profileBadCountFiberConstant
profileBadCountRepresented_of_profileBadCountFiberConstant
profileBadCountFiberConstant_of_profileBadCountRepresented
profileBadCountRepresented_iff_profileBadCountFiberConstant_of_repInFiber
profileBadCountRepresented_of_zero_oscillation
profileFiberOscillationBounded_zero_of_profileBadCountRepresented
profileFiberOscillationBounded_zero_iff_profileBadCountRepresented_of_repInFiber
worstCaseIncidenceBounded_of_profileBadCountRepresented_budget
deltaStar_pin_of_profileBadCountRepresented_budget
worstCaseIncidenceBounded_of_profileBadCountFiberConstant_budget
deltaStar_pin_of_profileBadCountFiberConstant_budget
profileFiberOscillationCertificate_zero_iff_profileBadCountRepresented_and_budget
not_profileBadCountFiberConstant_iff_exists_sameProfile_count_ne
not_profileBadCountRepresented_iff_exists_stack_count_ne
not_profileBadCountRepresented_and_zeroBudgeted_iff_exists_factor_miss_or_budget_lt
BadCountInjectiveOn
profile_injOn_of_profileBadCountFiberConstant_of_badCountInjectiveOn
card_le_profileCard_of_profileBadCountFiberConstant_badCountInjectiveOn
not_profileBadCountFiberConstant_of_profileCard_lt_badCountInjectiveOn
not_profileBadCountRepresented_of_profileCard_lt_badCountInjectiveOn
not_profileFiberOscillationBounded_zero_of_profileCard_lt_badCountInjectiveOn
```

The representative-free central equivalence is:

```text
ProfileFiberOscillationBounded F C delta profile (fun _ => 0)
  iff
ProfileBadCountFiberConstant F C delta profile.
```

With in-fiber representatives, this descends to the representative-dependent equivalence:

```text
ProfileRepresentativeInFiber profile rep
  ->
ProfileFiberOscillationBounded F C delta profile (fun _ => 0)
  iff
ProfileBadCountRepresented F C delta profile rep.
```

The representative-free direct consumer is:

```text
ProfileBadCountFiberConstant
  + in-fiber representative section
  + used representative budget
  -> WorstCaseIncidenceBounded
  -> delta-star lower pin.
```

Equivalently, after choosing in-fiber representatives:

```text
ProfileBadCountRepresented
  + used representative budget
  -> WorstCaseIncidenceBounded
  -> delta-star lower pin.
```

## Refutation Surface

The exact negative form says a zero-slack factorization-plus-budget proof fails for precisely one of
two reasons:

```text
1. some stack has a bad count different from its profile representative;
2. some used profile representative is above the budget B.
```

So a scanner for a proposed zero-slack profile should not search vaguely for "profile instability".
It should first look for the representative-free concrete witness:

```text
profile u = profile v
and
StackBadCount u != StackBadCount v.
```

If representatives have already been chosen, the same failure can be tested as:

```text
StackBadCount u != StackBadCount (rep (profile u)).
```

If that witness exists, the zero-slack middle case is dead for that profile.

## Continuation: cardinality gate for distinct bad counts

The zero-slack route now also has a profile-cardinality refutation:

```lean
BadCountInjectiveOn
profile_injOn_of_profileBadCountFiberConstant_of_badCountInjectiveOn
card_le_profileCard_of_profileBadCountFiberConstant_badCountInjectiveOn
not_profileBadCountFiberConstant_of_profileCard_lt_badCountInjectiveOn
not_profileBadCountRepresented_of_profileCard_lt_badCountInjectiveOn
not_profileFiberOscillationBounded_zero_of_profileCard_lt_badCountInjectiveOn
```

If a finite scanner family `U` has pairwise distinct bad-scalar counts, then any zero-slack profile
must be injective on `U`.  Therefore `U.card <= Fintype.card P`.  If a proposed compressed profile
has fewer labels than the distinct-count family, fiberwise bad-count constancy and representative
factorization are both impossible.

This gives a cheaper first-pass falsifier for concrete profiles: find more distinct bad-count values
than the profile has labels before searching for a same-profile unequal-count pair.

## Critical Consequence

This does not close the floor.  It removes one possible ambiguity in the profile route.

The profile route can now be sorted into three honest cases:

```text
zero slack:
  prove fiberwise bad-count constancy;
  equivalently, after choosing in-fiber representatives,
  prove exact bad-count factorization through the profile representatives;

small positive slack:
  prove a genuine same-fiber oscillation theorem with diameter <= slack;

large slack:
  the representative-plus-slack budget is likely as hard as the original worst-stack bound.
```

The current literature/PDF trail still does not provide a theorem of any of these three forms.  The
new socket is useful because it gives the next probe loop a crisp falsifier: if a proposed algebraic
profile is meant to be zero-slack, one unequal same-profile representative count refutes it.

## Continuation: cardinality pressure

The zero-slack route now has a finite cardinality obstruction.  If a scanner family `U` has
pairwise distinct bad-scalar counts, recorded as `BadCountInjectiveOn`, then any zero-slack profile
must be injective on `U`.  Consequently:

```text
U.card <= Fintype.card P.
```

So a proposed compressed profile with fewer labels than such a family cannot have zero slack.
The new refuters kill all three zero-slack formulations: representative-free fiber constancy,
representative factorization, and zero same-profile oscillation.  This does not touch positive
slack, but it gives probes a cheap size test before trying to prove a delicate same-fiber
oscillation theorem.

## Next Attack

The best remaining profile attempt should now choose a concrete compressed invariant and test it
against this factorization criterion before trying analytic estimates.  Candidate invariants worth
probing are period/Jacobi data, orbit-normal forms, and the finite floor-localization patterns.

If none of those profiles satisfy exact factorization on verified rungs, then any surviving profile
proof must be a positive-slack oscillation theorem.  That pushes the proof obligation back toward the
same anti-resonance/BGK-Paley machinery already identified in the issue.
