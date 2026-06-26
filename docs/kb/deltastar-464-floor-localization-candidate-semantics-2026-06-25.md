# Issue #464: Floor Localization Candidate-List Semantics

Date: 2026-06-25

Status: semantic guardrail for the off-BGK bad-prime lane; not a prize proof.

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AssaultV2_FloorLocalizationN32.lean`

## Point

The bad-prime localization lane compares a finite candidate list, such as the `n=32` list `[97]`,
against the least split prime.  That comparison is only list arithmetic.  It does not, by itself,
prove that the list is extensionally equal to the true finite-field floor-bad predicate.

The new declarations separate the two levels:

```lean
CandidateListSoundInAP
CandidateListCompleteInAP
CandidateListExactInAP
```

`CandidateListExactInAP FloorBad n candidates` is the actual semantic proof obligation supplied by
an exhaustive rank scanner: for every split prime, `FloorBad n p` holds exactly when `p` is listed.

## Result

The file proves:

```lean
candidateListExactInAP_iff_sound_complete
```

so exactness is precisely soundness plus completeness.

It also proves a countermodel:

```lean
floorBad32_candidate_match_not_extensional_evidence
```

The empty floor-bad predicate is enough to show that the fact
`floorBad32Conjectured = [smallestPrime1ModN 32 200]` is not extensional evidence about the true
floor-bad predicate.  The scanner semantics are the missing input.

Finally, it adds the honest bridge:

```lean
floorLocalizationUniform_of_candidateListExactSmallest
```

If every dyadic rung has an exact candidate list consisting of the least split prime, then the
uniform localization predicate follows.

## Consequence For #464

This keeps the off-BGK floor-localization lane useful but precise.  The next proof obligation is not
another `by decide` check on a candidate list; it is an exact rank-scanner theorem, or a mathematical
replacement for that scanner, proving soundness and completeness for the true floor-bad predicate.
