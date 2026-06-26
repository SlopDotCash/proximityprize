# Issue #464 loop note: floor closure as a field-level trichotomy

Date: 2026-06-26.

Status: **interface progress and refutation sharpening**, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The off-BGK bad-prime/localization route should no longer be described as one theorem.  It is a
three-part certificate at the actual prize field:

```text
not FloorBad(2^a, |F|)
FamilyBounded F C delta R B
FamilyDominates F C delta R
```

The first part is arithmetic obstruction removal.  The second is a floor-to-family budget theorem.
The third is the real universal-incidence theorem: the proposed floor/profile family must contain a
global maximizer of `StackBadCount`, equivalently dominate every stack.

## Invented Tool

I added the field-level certificate:

```lean
FloorClosureAtField
```

in

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorClosureContract.lean
```

It deliberately sits after the Linnik/TZ arithmetic layer.  If localization and least-prime supply
prove that the current field is floor-good, and if floor-goodness budgets the selected family, and if
that family dominates, then the certificate feeds:

```lean
worstCaseIncidenceBounded_of_floorClosureAtField
deltaStar_pin_of_floorClosureAtField
```

This is a positive route, but it exposes the full cost.  The arithmetic theorem alone does not touch
`WorstCaseIncidenceBounded`; it only helps build the first conjunct.

## Attempt

The optimistic idea was:

```text
TZ / least-prime supply
  -> not FloorBad at prize primes
  -> selected binder/floor family is budgeted
  -> selected family dominates all stacks
  -> delta-star lower pin
```

The Lean contract shows exactly where the optimism must become mathematics.  `not FloorBad` does not
even mention arbitrary `WordStack`s.  `WorstCaseIncidenceBounded` is an all-stack statement.  The
only bridge is a real domination or global-max-containment theorem.

## Refutation Surface

The useful new theorem is the exact failure form:

```lean
not_floorClosureAtField_iff_bad_or_member_budget_lt_or_each_member_beaten
```

It says a concrete floor-closure certificate fails exactly when one of these holds:

```text
1. FloorBad(2^a, |F|);
2. some representative r in R is above budget;
3. every representative r in R is beaten by some stack u.
```

This is stronger than the earlier warnings.  It gives a scanner three finite target types.  In
particular, once the arithmetic layer succeeds, the route has only two remaining failure modes:
budget miss or domination miss.  The domination miss is local in the candidate family: each proposed
representative can be refuted by its own beating stack.

## Critique

This loop does not find the floor proof.  It eliminates a false middle state.

There is no meaningful claim of the form:

```text
the floor bad-prime obstruction closes, therefore the prize floor follows.
```

The correct field-level certificate either contains the all-stack domination content or it does not.
If it does not, the theorem itself decomposes the failure into a concrete countercertificate.

## New Math Still Needed

The next non-redundant theorem is not another least-prime wrapper.  It is one of:

```text
FamilyContainsGlobalMax F C delta R
```

for the explicit floor/profile family, or a direct all-stack incidence theorem.  In prose:

```text
every worst stack has a normal form represented by the floor/profile family.
```

That would be genuinely new sparse-incidence/classification mathematics.  Without it, the
bad-prime-localization lane remains valuable obstruction removal and a clean scanner target, but not
a proof of the δ* floor.
