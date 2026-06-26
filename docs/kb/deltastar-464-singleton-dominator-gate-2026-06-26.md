# Issue #464: Singleton Dominator Gate For The Off-BGK Floor

Date: 2026-06-26

## Claim Tested

The floor-localization lane has a real arithmetic core: for the modeled binder/floor predicate,
the bad primes appear to be the single least prime `1 mod 2^a`.  The dossier and the live issue both
stress the correction: this is obstruction removal, not a proof of the delta-star floor, because
`epsMCA` is governed by a supremum over all stacks.

This pass isolates the exact singleton bridge that would be needed to make the binder/floor family
sufficient:

```text
one distinguished floor direction is bounded
+ that direction globally maximizes the bad-scalar count
=> every direction is bounded.
```

Without the second line, the argument is just a lower-bound surface pretending to be an upper-bound
surface.

## Formal Result

The frontier guardrail

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/FloorNecessaryNotSufficient.lean
```

now defines:

```lean
OneDirectionMaximizes bad i0
```

meaning every direction's bad-scalar set has cardinality at most that of the distinguished direction
`i0`.

The new theorem

```lean
allDirectionsBounded_of_oneDirectionBounded_and_maximizes
```

is the precise positive replacement for the invalid shortcut:

```text
OneDirectionBounded bad i0 B
OneDirectionMaximizes bad i0
--------------------------------
AllDirectionsBounded bad B
```

The scanner-facing falsifier is:

```lean
not_oneDirectionMaximizes_iff_exists_larger
```

so a proposed singleton floor representative fails as a domination proof exactly when some other
direction has a strictly larger bad-scalar count.

## Critical Essay

The previous floor story was too easy in exactly one place.  It was tempting to say:

```text
least-prime localization closes the binder floor
=> the prize floor is closed.
```

That implication has the wrong polarity.  The binder family contributes one term under a global
supremum.  It can witness badness, and it can remove a known obstruction, but it cannot cap the
supremum unless it is itself worst-case.

The new tool is deliberately small: `OneDirectionMaximizes` is not a number-theory statement.  It is
the missing extremality theorem that any floor proof must provide after the arithmetic is done.
This keeps three tasks separate:

```text
1. arithmetic localization: which primes are binder-floor bad?
2. binder budget: what is the bad-scalar count of that family?
3. extremality/domination: why is no other stack worse?
```

Task 1 may be off-BGK.  Task 3 is where the Paley/BGK wall can re-enter, because it asks for a
universal worst-case statement over all directions.  A successful proof must either prove
`OneDirectionMaximizes` for the actual binder family, replace it by a finite family with
`FamilyContainsGlobalMax`, or bypass the floor family and prove `WorstCaseIncidenceBounded`
directly.

## Attack Plan

The next useful probes should not merely re-check whether `p = 97` is floor-bad at `n = 32`.
They should search for counter-directions:

```text
for each verified floor-good prime p:
  compute binder/floor bad count B0
  scan broader stack families or profile representatives
  report any direction with count > B0
```

A single such direction refutes the singleton bridge for that finite rung.  If none appear, the
right conjecture is no longer "floor-bad primes localize"; it is:

```text
the binder/floor direction is a global maximizer at the relevant radius.
```

That is the conjecture that would actually connect the off-BGK arithmetic lane to the delta-star
floor.
