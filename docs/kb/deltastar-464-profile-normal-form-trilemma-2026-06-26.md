# Issue #464 loop note: profile normal forms and the exact trilemma

Date: 2026-06-26.

Status: **attack/refutation progress**, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The most plausible off-BGK proof shape left after the floor-localization and orbit-cover batches is a
stack normal-form theorem:

```text
profile : WordStack A (Fin 2) iota -> P
cap : P -> Nat
```

with

```text
StackBadCount F C delta u <= cap (profile u)
```

for every stack `u`.  If all caps are within the budget, the direct route proves
`WorstCaseIncidenceBounded`.  If used profile caps are realized by bounded representatives, the
representative route proves it.

This is the honest version of many informal proposals:

```text
adjacent pattern / binder type / floor-good class / monomial orbit / refined profile
  -> finite catalogue
  -> all stacks are no worse than a catalogue representative
```

The new Lean trilemmas make the route falsifiable instead of rhetorical.

## New Machine Surface

The profile interface now has combined exact negative forms:

```lean
not_profileCaps_and_profileBudgeted_iff_exists_counterexample_or_counterprofile
not_profileRealizedByReps_iff_exists_counterprofile
not_profileCaps_and_profileRealizedByFamily_and_familyBounded_iff_exists_counterexample_or_counterprofile_or_member_budget_lt
not_profileCaps_and_profileRealizedByReps_and_familyBounded_iff_exists_counterexample_or_counterprofile_or_member_budget_lt
```

The direct certificate

```lean
ProfileCaps F C delta profile cap and ProfileBudgeted cap B
```

fails exactly by one of:

```text
1. a stack u with cap(profile u) < StackBadCount F C delta u;
2. a profile p with B < cap p.
```

The representative certificate

```lean
ProfileCaps F C delta profile cap
and ProfileRealizedByFamily F C delta profile cap R
and FamilyBounded F C delta R B
```

fails exactly by one of:

```text
1. a stack above its assigned cap;
2. a used profile whose cap is larger than every proposed representative;
3. an above-budget representative.
```

For a profile-indexed representative map `rep : P -> WordStack A (Fin 2) iota`, the second witness
specializes to

```text
UsedProfile profile p and StackBadCount F C delta (rep p) < cap p.
```

## Attempted New Tool

The proposed tool is a **profile domination theorem**.  It would not need to identify a unique
global maximizer.  It would only need to show that every stack collapses to a profile cap, and that
the cap is either directly budgeted or reached by a bounded representative.

The useful theorem would look like:

```text
forall u, StackBadCount(u) <= cap(profile(u))
forall used p, exists r in R, cap(p) <= StackBadCount(r)
forall r in R, StackBadCount(r) <= B
```

This is stronger than a finite scanner over nice examples and weaker than a single global dominator.
It is the natural middle ground between the one-stack certificate and the full BGK/Paley sup bound.

## Refutation Pressure

The profile route now has no ambiguous failure state.

If a proposed adjacent-pattern or binder profile is wrong, a scanner should return a concrete stack
whose bad-scalar count exceeds the assigned cap.  If the cap theorem is true but the finite catalogue
is not sufficient, the scanner should return a used profile whose cap is not realized by any
representative.  If both are true but the budget is too aggressive, it returns an above-budget
representative.

That is a useful decomposition because the three failures demand different mathematics:

```text
counter-stack: profile is too coarse;
counter-profile: representatives do not realize the profile maxima;
above-budget representative: floor/localization budget is too optimistic.
```

## Literature Check

The local PDF corpus and issue dossier do not currently provide a theorem with this output type.

The list-decoding papers provide Johnson-side machinery, positive/negative proximity-gap
constructions, or algorithmic folded-RS subspace pruning.  None of those says that arbitrary smooth
RS MCA stacks are dominated by a finite binder/floor profile.  The Paley/BGK papers provide
character-sum cancellation statements, medium-range subgroup estimates, spectral identifications, or
distributional/equidistribution inputs.  None of those supplies a profile cap theorem below the
thin-subgroup sup-norm wall.

So this route is not closed by literature import.  It remains a possible new-math formulation, but
the missing theorem is exactly visible.

## Verdict

This loop does not close the floor.  It sharpens the strongest off-BGK normal-form strategy into a
closed certificate and exact falsifiers.

The next productive attack is empirical and formal at once:

```text
Pick a proposed profile map.
Define its cap.
Try to prove ProfileCaps.
If it fails, extract the counter-stack witness.
If it holds, try to realize used profile caps by a bounded representative family.
```

Until a profile map survives that trilemma, a finite floor catalogue is not a proof of
`WorstCaseIncidenceBounded`; it is only a source of candidate representatives.
