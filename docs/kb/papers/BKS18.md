---
kind: paper
bibkey: BKS18
title: "Worst-case to average case reductions for the distance to a code"
year: "2018"
bib_source: website/blueprint/src/references.bib
source_metadata: ../sources/BKS18/metadata.yml
status: mapped
---

# BKS18

## At A Glance

ArkLib cites this work for collinearity counting along an affine pencil. The
formalization bounds the number of challenges whose agreement sets contain a
coordinate that disagrees with the aligned codeword pair.

## What ArkLib Uses From This Paper

- `CodingTheory.card_le_add_one_of_pencil_mismatch` gives the root-set count.
- `CodingTheory.IsLineDecodable.mcaError_le_of_floor_add_two` uses the count to
  convert aligned line decoding to a mutual correlated agreement bound.

## Main ArkLib Touchpoints

[LineDecoding.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecoding.lean)

## Source Access

[Source metadata](../sources/BKS18/metadata.yml)
