# Issue #464: line-list budget gate for ratio-census attacks

Date: 2026-06-26.

Status: **scanner-interface progress**, not a delta-star proof.

## Thesis

The ratio-census and per-codeword heavy-scalar files already prove the local part of the affine-line
story: a fixed codeword can be close to only `floor(n/a)` scalars on a line when the direction is
nonzero coordinatewise.  The remaining positive obligation is not another ratio identity.  It is a
line-list-size theorem: how many codewords appear anywhere along the affine line.

This pass names that boundary directly in:

```text
ArkLib/Data/CodingTheory/ProximityGap/LineListReduction.lean
```

## New API

The local sets are now first-class declarations:

```lean
lineBadScalars
lineAppearingCodewords
LineListBudgeted
```

The positive consumer is:

```lean
lineBadScalars_card_le_of_lineListBudgeted
```

It states the exact budget law:

```text
lineAppearingCodewords.card <= L
=> lineBadScalars.card <= L * floor(n/a)
```

The old theorem `badScalar_card_le_lineList_mul` already contained this argument internally.  The
new form is meant for downstream scanners and proof attempts that want to supply a candidate
line-list bound without unfolding the bipartite cover proof.

## Refutation Surface

The scanner-facing contrapositives are:

```lean
not_lineListBudgeted_of_lineBadScalars_card_gt
lineAppearingCodewords_card_gt_of_lineBadScalars_card_gt
```

So any over-budget line:

```text
L * floor(n/a) < lineBadScalars.card
```

does not falsify the per-codeword ratio-census layer.  It proves instead that the affine line has
more than `L` appearing codewords.  The obstruction is an oversized line list.

## Consequence

This is a useful audit split.  Ratio-census identities, Markov-on-support bounds, and
heavy-scalar lemmas can bound each codeword's scalar contribution.  They cannot by themselves
control how many codewords appear along the whole line.

The remaining non-tautological route is therefore:

```text
prove a subtrivial bound on lineAppearingCodewords.card
```

for the deployed affine lines, or produce a scanner witness showing that any proposed bound `L` is
too small.  That is exactly the affine-line list-decoding core, not a floor/localization shortcut.

## Literature/PDF Inventory Note

The local scan covered 327 PDFs under `/Users/shawwalters/papers/arklib` and 10 PDFs under
`docs/references/proximity-gap-paley-spectrum`, 337 total across those two corpora.  The relevant
Littlewood-Offord, character-sum, and list-decoding notes keep returning to the same split:
anti-concentration controls one line/codeword interaction, while the prize-scale closure still
needs a production line-list bound.  No paper in this pass supplied that missing bound as a theorem
ready to plug into `LineListBudgeted`.
