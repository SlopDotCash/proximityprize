# Issue #464: floor successor propagation gate

Date: 2026-06-26.

Status: **refutation-surface progress**, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The off-BGK floor lane depends on a uniform floor-localization input: for every dyadic rung
`a >= 4`, the singleton list

```text
[smallestPrime1ModN (2^a) (2^(5*a))]
```

must be extensionally exact for the floor-bad predicate inside the split-prime family.

Finite checked rungs do not provide that uniform theorem.  The useful non-tautological target is the
successor propagation step:

```text
CandidateListExactAt a
  -> CandidateListExactAt (a + 1)
```

This pass makes the positive and negative sides of that target explicit.

## Lean Additions

In `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorClosureContract.lean`:

```lean
not_candidateListExactSmallestFamily_iff_exists_rung_not_exact
not_candidateListExactSuccessor_iff_exists_exact_rung_next_fails
not_candidateListExactSmallestFamily_of_next_failure
```

The existing positive sockets are:

```lean
CandidateListExactAt
CandidateListExactSuccessor
candidateListExactSmallestFamily_of_base_and_successor
candidateListExactSmallestFamily_of_prefix_and_successor
floorLocalizationUniform_of_candidateListExactSmallestFamily
```

Together, these say that a base rung plus a real successor theorem gives the uniform
floor-localization input consumed by the Linnik and Thorner-Zaman floor contracts.

The promoted bridge module
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/FloorClosureSuccessorScanner.lean` now connects the
generic finite-rung scanner from `FloorFiniteRungUniformityBarrier.lean` back to this concrete
floor-closure predicate:

```lean
candidateListExactSmallestFamily_iff_uniformFrom_candidateListExactAt
candidateListExactSuccessor_iff_successorStep_candidateListExactAt
candidateListExactSmallestFamily_iff_base_and_successor
not_candidateListExactSmallestFamily_iff_not_base_or_exists_exact_rung_next_fails
not_candidateListExactSmallestFamily_iff_exists_exact_rung_next_fails_of_base
candidateListExactSmallestFamily_of_verifiedPrefix_and_successorStep
candidateListExactSmallestFamily_of_verifiedOn_Icc_and_successorStep
not_candidateListExactSuccessor_of_verifiedPrefix_of_not_candidateListExactSmallestFamily
not_candidateListExactSuccessor_of_verifiedOn_Icc_of_not_candidateListExactSmallestFamily
exists_exact_rung_next_fails_of_verifiedPrefix_of_not_candidateListExactSmallestFamily
exists_exact_rung_next_fails_of_verifiedOn_Icc_of_not_candidateListExactSmallestFamily
exists_candidate_exact_next_failure_at_or_after_cutoff
exists_candidate_exact_next_failure_at_or_after_cutoff_Icc
```

Thus finite verified-prefix evidence has one precise escape hatch: if it does not extend to
uniform singleton exactness, the concrete successor theorem must fail at an adjacent rung.
The latest normal form is sharper:

```text
CandidateListExactSmallestFamily
  iff CandidateListExactAt 4 and CandidateListExactSuccessor.
```

So after the base rung is exact, uniform failure is equivalent to an adjacent exact-then-failing
rung.  If the base rung is not exact, the scanner has already refuted the route at `a = 4`.
The cutoff-refined scanner variants additionally show that, once a prefix through `cutoff` is
verified, the adjacent exact-then-failing pair can be placed at some `a >= cutoff`.

The public consumer bridge
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/FloorClosurePrefixConsumer.lean` composes this
prefix-plus-successor input with the sharp Linnik/TZ budgeted-global-max contracts:

```lean
worstCaseIncidenceBounded_of_linnik_prefix_successor_budgetedMax
deltaStar_pin_of_linnik_prefix_successor_budgetedMax
worstCaseIncidenceBounded_of_tz_prefix_successor_budgetedMax
deltaStar_pin_of_tz_prefix_successor_budgetedMax
```

Thus the floor lane can now be stated without an intermediate uniform-localization hypothesis:
verified prefix + successor theorem + least-prime supply + budgeted global maximizer feeds the
same `WorstCaseIncidenceBounded` and delta-star consumers.

## Refutation Surface

Uniform singleton exactness now fails exactly by either base failure or an adjacent successor
failure:

```text
not CandidateListExactAt 4
or
exists a >= 4,
  CandidateListExactAt a
  and not CandidateListExactAt (a + 1)
```

The successor theorem fails by an adjacent pair:

```text
exists a >= 4,
  CandidateListExactAt a
  and not CandidateListExactAt (a + 1)
```

So a scanner should not merely accumulate more isolated exact rungs.  It should either prove the
successor step from the arithmetic of the smallest `1 mod 2^a` prime, or search for an adjacent
exact-then-failing pair.

## Consequence

This does not touch the BGK/Paley incidence core.  It sharpens the only off-BGK bad-prime
localization lever into a refutable tower contract.

The honest next floor attack is now:

```text
prove CandidateListExactSuccessor
```

or produce the adjacent-rung counterexample named above.  Without one of those, the verified
`a = 4,5` evidence remains finite evidence and cannot be promoted to the uniform
`FloorLocalizationUniform` hypothesis used by the floor-closure contracts.

## Continuation: split-prime mismatch scanners

The base localization file now exposes the concrete finite-prime witnesses behind these gates:

```lean
not_candidateListExactInAP_iff_exists_split_prime_mismatch
not_floorLocalizationUniform_iff_exists_rung_prime_mismatch
not_LinnikLeastPrimeBelowPrize_iff_exists_rung_prize_le
```

So the off-BGK floor lane has three independent falsifier types:

```text
1. a true floor-bad split prime missing from the singleton list;
2. the singleton least split prime is not floor-bad;
3. the searched least split prime is not below prize scale.
```

This is the exact scanner contract for the least-prime route.  A future probe result should return
one of these witnesses, not just a prose statement that a rung "failed".
