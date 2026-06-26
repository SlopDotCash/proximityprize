---
kind: paper
bibkey: BCHKS25
title: "On Proximity Gaps for {Reed--Solomon} Codes"
year: "2025"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2025/2055
source_metadata: ../sources/BCHKS25/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean
  - ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean
  - ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean
  - ArkLib/ToMathlib/Bridge2BCHKS25.lean
---

# BCHKS25

## At A Glance

`BCHKS25` is the Ben-Sasson, Carmon, Habock, Kopparty, and Saraf proximity-gaps paper
recorded in `references.bib` as ePrint 2025/2055 and mirrored as ECCC TR25-169.
For ArkLib, it is both a Johnson-range positive input and a barrier map: it improves known
Reed-Solomon proximity-gap parameters up to the Johnson radius, gives sharp negative evidence near
and beyond Johnson, and ties stronger proximity gaps to stronger list-decoding bounds.

## What ArkLib Uses From This Paper

- Johnson-range RS proximity-gap/MCA bounds with improved exceptional-set size.
- The near-capacity and Johnson-jump negative statements used by the `mcaDeltaStar` bracket
  adapters.
- The list-decoding implication: stronger proximity gaps beyond Johnson require corresponding
  beyond-Johnson list-decoding progress.
- The subgroup-sumset/admissibility route tracked elsewhere in the KB as the BCHKS25 Conjecture
  1.12 lane.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean)
  names the external RS proximity-gap and capacity-bound statements.
- [`ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean`](../../../ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean)
  carries the proximity-gap-to-list-decoding bridge shape.
- [`ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean)
  adapts BCHKS-style bounds into `mcaDeltaStar` witnesses.
- [`ArkLib/ToMathlib/Bridge2BCHKS25.lean`](../../../ArkLib/ToMathlib/Bridge2BCHKS25.lean)
  contains the bad-line witness interface used by downstream consumers.

## Version Notes

- `references.bib` records the ePrint key `2025/2055`; the accessible paper copy used in KB
  routing is also identified as ECCC TR25-169.
- Several older KB notes call this source "BChKS" or refer to the ECCC number directly; treat those
  as aliases for `BCHKS25`.

## Known Divergences From ArkLib

- The paper's positive Johnson-range bounds are not the prize floor. Issue #464 asks for the
  smooth-domain interior floor past Johnson, where the current dossier still reduces to the
  Paley/BGK character-sum wall.
- Some negative examples in the paper use additive or characteristic-2 structure. ArkLib's prize
  target is the explicit dyadic multiplicative subgroup in large prime fields, so those examples are
  routed as barriers or near-misses unless a separate transfer theorem is present.
- Several in-tree declarations are external `Prop` front doors or witness packages rather than
  full formalizations of the paper proofs.

## Open Formalization Gaps

- Formalize the BCHKS25 Johnson-range interpolation proof rather than carrying it only as an
  external capacity-bound statement.
- Close or refute the BCHKS25 Conjecture 1.12 / subgroup-sumset lane for the exact smooth-domain
  prize regime.
- Separate which BCHKS negative constructions transfer to multiplicative subgroup domains over
  large prime fields and which are only structural warnings.

## Source Access

- Source metadata: [`../sources/BCHKS25/metadata.yml`](../sources/BCHKS25/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
