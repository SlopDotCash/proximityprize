# Issue #464: finite candidate families reduce to their own maximum

Date: 2026-06-25.

Status: **guardrail progress**, not a delta-star proof.

## Claim Tested

The floor-localization lane might propose not one binder stack, but a finite catalogue `R` of
candidate stack shapes.  The honest question is whether this list can replace the universal
incidence input:

```text
WorstCaseIncidenceBounded C delta B.
```

It can, but only under a domination theorem:

```text
for every stack u, some r in R has
StackBadCount(u) <= StackBadCount(r).
```

## Formal Result

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_StackCandidateFamilyMax.lean
```

now defines:

```lean
FamilyBounded
FamilyDominates
IsFamilyMax
```

and proves:

```lean
not_familyBounded_iff_exists_member_budget_lt
exists_familyMax_of_nonempty
familyDominates_iff_familyMax_dominates
worstCaseIncidenceBounded_of_familyDominates
worstCaseIncidenceBounded_iff_familyBounded_of_familyDominates
familyBounded_iff_familyMaxBounded
worstCaseIncidenceBounded_iff_familyMaxBounded_of_familyDominates
deltaStar_pin_of_familyDominates
not_familyDominates_of_counterexample
not_familyDominates_of_exists_strictly_larger_than_all
familyBounded_and_counterStack_not_worstCaseIncidenceBounded
familyBounded_not_dominationProof_of_exists_strictly_larger_than_all
```

The key point is that a nonempty finite family has an internal maximizer `rMax`.  Once the family
dominates all stacks, the full open-core worst-case bound is equivalent either to bounding every
member of the family or to bounding just `rMax`.

## Refutation Test

The file also gives the clean falsification API:

```lean
not_familyBounded_iff_exists_member_budget_lt
not_familyDominates_of_exists_strictly_larger_than_all
```

So a finite binder catalogue has two exact failure modes:

```text
FamilyBounded R B fails
  iff some listed representative r in R is above budget B.

FamilyDominates R fails by scanner witness
  if some outside stack u beats every listed representative.
```

A separate counter-stack whose bad count exceeds the budget kills the universal incidence hypothesis
even if every listed catalogue member is already bounded by that budget.

## Critical Verdict

This does not make the floor route easier.  It removes ambiguity about what a finite candidate list
must prove.

A finite binder/floor catalogue is useful only if its worst member is a true global dominator.
Bounding each convenient representative is insufficient by itself; the prize-facing theorem is the
classification or domination statement saying that no stack outside the catalogue has larger
bad-scalar count.

Thus the finite-family version of the missing #464 theorem is:

```text
the floor/binder catalogue contains, or dominates, the true maximizer of StackBadCount.
```

Without that theorem, the catalogue remains obstruction bookkeeping rather than a proof of
`WorstCaseIncidenceBounded`.
