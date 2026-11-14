---
kind: paper
bibkey: Hab25
title: "A note on mutual correlated agreement for {Reed-Solomon} codes"
year: "2025"
bib_source: website/blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2025/2110
source_metadata: ../sources/Hab25/metadata.yml
status: mapped
---

# Hab25

## At A Glance

The line-decoding development cites Lemma 1 for the correlated agreement form
of the affine-pencil root-set count. The BCIKS20 development cites Claim 1 for
the algebraic step that relates a common agreement witness to the code.

## What ArkLib Uses From This Paper

`CodingTheory.card_le_add_one_of_pencil_mismatch` formalizes the count in
[LineDecoding.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecoding.lean).

## Main ArkLib Touchpoints

- The heavy-point counting and affine pinning lemmas live in
  [Hab25HeavyPoints.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25HeavyPoints.lean).
- [Weld.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Weld.lean)
  records the hypotheses used for the algebraic step.

## Source Access

[Source metadata](../sources/Hab25/metadata.yml)
