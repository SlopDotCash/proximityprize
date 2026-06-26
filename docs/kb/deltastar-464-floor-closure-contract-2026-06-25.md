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
not_worstCaseIncidenceBounded_iff_exists_stack_budget_lt
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

which is now exactly equivalent to failure of the universal incidence conclusion at budget `B`.
This refutes the floor route even if floor-goodness bounded the listed floor family.

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

## Continuation: exact candidate lists are now the scanner-facing input

The closure contract now has direct consumers for the stronger scanner obligation:

```lean
CandidateListExactSmallestFamily FloorBad
```

This means: for every dyadic rung `a >= 4`, the true floor-bad predicate is extensionally equal,
inside the split-prime family, to the singleton list

```lean
[smallestPrime1ModN (2^a) (2^(5*a))]
```

This is intentionally stronger than checking that a proposed list matches the least-prime rule.
The `n = 32` singleton `[97]` can match the rule while still failing to be semantic evidence for
the true floor-bad predicate; `_AssaultV2_FloorLocalizationN32.lean` now formalizes that countermodel.

The new contract theorems are:

```lean
familyBounded_of_linnik_candidateListExactSmallest
worstCaseIncidenceBounded_of_linnik_candidateListExactSmallestContract
deltaStar_pin_of_linnik_candidateListExactSmallestContract
familyBounded_of_tz_candidateListExactSmallest
worstCaseIncidenceBounded_of_tz_candidateListExactSmallestContract
deltaStar_pin_of_tz_candidateListExactSmallestContract
```

So the current best off-BGK route is exactly:

```text
exact singleton scanner evidence
+ sub-4 least-prime supply (Linnik-strength/TZ-strength)
+ floor-good -> family budget
+ family domination
+ scaled MCA budget
=> delta-star lower pin
```

The failure modes are equally sharp:

```text
scanner cannot prove extensional exactness
or floor-goodness does not budget the chosen family
or an outside stack beats the family
or the budget is too large after scaling by |F|
```

This does not move the BGK/Paley wall.  It makes the off-BGK floor lane audit-complete: every future
scanner certificate or counterexample has a named Lean socket and a clear proof obligation.

## Continuation: successor propagation

The uniform exactness side now has a positive tower socket:

```lean
CandidateListExactAt
CandidateListExactSuccessor
candidateListExactSmallestFamily_of_base_and_successor
candidateListExactSmallestFamily_of_prefix_and_successor
```

So the two verified rungs `a = 4,5` are not being treated as evidence-by-extrapolation.  They become
useful only if paired with a successor theorem:

```text
CandidateListExactAt a
=> CandidateListExactAt (a+1)
```

That successor step is the missing tower/renormalization mathematics for the floor scanner.  Without
it, finite-rung evidence remains finite-rung evidence.

## Continuation: exhaustive-family calibration

The contract also names the tautological all-stack endpoint:

```lean
familyDominates_univ
worstCaseIncidenceBounded_iff_familyBounded_univ
deltaStar_pin_of_exhaustiveFamilyBounded
```

The exhaustive family of all stacks dominates by reflexivity, and bounding that family is exactly
the original universal incidence hypothesis.  This is deliberately not a new compressed proof
route; it is the calibration point.  An exhaustive all-stack scanner certificate would be enough,
but it is just the original open core in finite form.

The off-BGK floor lane therefore has two honest choices:

```text
certify the all-stack family directly,
or prove that a much smaller floor/profile family dominates the all-stack family.
```

Anything in between is only evidence.  A candidate floor family that is bounded but not known to
dominate all stacks cannot feed `mcaDeltaStar`.

## Continuation: domination means containing a global maximizer

The finite-family condition has now been sharpened again:

```lean
FamilyContainsGlobalMax
familyDominates_of_containsGlobalMax
containsGlobalMax_of_familyDominates
familyDominates_iff_containsGlobalMax
worstCaseIncidenceBounded_of_containsGlobalMax
deltaStar_pin_of_containsGlobalMax
not_familyDominates_of_each_member_beaten
floorGood_familyBudget_not_dominationProof_of_each_member_beaten
```

For this actual `StackBadCount` order, `FamilyDominates C delta R` is equivalent to saying that
`R` contains a true global maximizer of the MCA bad-scalar count.  The internal maximum of a
dominating family is a global maximum; conversely a family containing a global maximum dominates
tautologically.

This turns the floor/profile task into a sharper theorem:

```text
the proposed floor family must contain a worst stack,
or every proposed representative can be beaten by some stack and domination fails.
```

The new local refutation hook no longer requires one witness beating the whole family at once.
It is enough to show:

```lean
∀ r ∈ R, ∃ u, StackBadCount r < StackBadCount u
```

That is the scanner target to falsify a proposed compressed floor catalogue.  It also clarifies why
least-prime floor-goodness is only obstruction removal: it can budget a family, but unless that
family contains a global worst stack, it is not a `WorstCaseIncidenceBounded` proof.

The Linnik and Thorner-Zaman candidate-list contracts now have equivalent global-max forms:

```lean
worstCaseIncidenceBounded_of_linnik_candidateListExactSmallestMaxContract
deltaStar_pin_of_linnik_candidateListExactSmallestMaxContract
worstCaseIncidenceBounded_of_tz_candidateListExactSmallestMaxContract
deltaStar_pin_of_tz_candidateListExactSmallestMaxContract
```

So the floor lane can state its final combinatorial obligation either as `FamilyDominates` or as
`FamilyContainsGlobalMax`; they are mathematically equivalent, but the latter is the clearer scanner
target.

## Continuation: max-containment consumers

The contract now lets downstream scanners or classification proofs feed the strongest operational
condition directly:

```lean
worstCaseIncidenceBounded_of_containsGlobalMax
deltaStar_pin_of_containsGlobalMax
worstCaseIncidenceBounded_of_linnik_candidateListExactSmallestMaxContract
deltaStar_pin_of_linnik_candidateListExactSmallestMaxContract
worstCaseIncidenceBounded_of_tz_candidateListExactSmallestMaxContract
deltaStar_pin_of_tz_candidateListExactSmallestMaxContract
floorGood_familyBudget_not_dominationProof_of_each_member_beaten
```

This removes the last ambiguity in the floor contract.  The positive route can be stated without
the softer word "domination":

```text
exact singleton scanner evidence
+ sub-4 least-prime supply
+ floor-good -> family budget
+ the family contains a true global bad-scalar maximizer
+ scaled MCA budget
=> delta-star lower pin
```

The negative route is equally local:

```text
for every proposed representative r, find some stack u_r with a larger bad-scalar count
=> the family contains no global maximizer
=> the bounded floor family is not a prize proof.
```

This is still not a proof of the floor.  It is a cleaner attack socket: the next scanner pass should
either certify that the proposed floor/profile family contains a global maximizer, or produce the
memberwise beating witnesses that refute that compressed family.

## Continuation: memberwise beating is an exact iff

The scanner refutation target has been tightened from a sufficient condition to an exact
characterization:

```lean
not_familyContainsGlobalMax_iff_each_member_beaten
not_familyDominates_iff_each_member_beaten
```

For a finite candidate family `R`,

```text
¬ FamilyDominates F C delta R
```

is equivalent to

```text
∀ r ∈ R, ∃ u, StackBadCount F C delta r < StackBadCount F C delta u.
```

So there are now only two outcomes for a proposed compressed floor catalogue:

```text
some representative is a true global maximizer,
or every representative can be beaten by an explicit outside stack.
```

This is the cleanest scanner interface so far.  It turns the next computational attack into a
finite, local certificate problem over the proposed representatives instead of a vague search for
"a better stack."

## Continuation: floor-good budget failure is exact

The budget side now has the same scanner-facing exactness:

```lean
not_familyBounded_iff_exists_member_budget_lt
not_floorGoodFamilyBudget_iff_floorGood_and_not_familyBounded
not_floorGoodFamilyBudget_iff_floorGood_and_exists_member_budget_lt
```

So failure of the missing floor-to-family budget theorem is not vague.  It is exactly:

```text
the modeled floor predicate is good at the field prime
and some selected representative r in R has StackBadCount r > B.
```

This isolates the off-BGK floor burden.  Least-prime localization may prove floor-goodness, but the
remaining budget theorem is a concrete above-budget-member exclusion for the chosen family.

## Continuation: universal budget failure is exact

The open-core incidence budget now has the same exact negative form:

```lean
not_worstCaseIncidenceBounded_iff_exists_stack_budget_lt
```

So `WorstCaseIncidenceBounded C delta B` fails exactly when some stack has bad-scalar count above
`B`.  This pins every floor-prize failure back to the same concrete scanner obligation: exclude all
above-budget stacks, not only the representatives in a proposed compressed family.
