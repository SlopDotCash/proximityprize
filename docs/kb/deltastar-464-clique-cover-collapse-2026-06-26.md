# delta* #464: clique-cover collapse under forbidden singleton edges

Date: 2026-06-26.

Status: negative structural theorem, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The singleton graph route now has a clean finite certificate: cover the actual
`codewordSingletonWitnessScalars` fiber by relation-cliques.  This is a good proof target for a
future interpolation relation, but it is not a weaker theorem statement once the forbidden-edge
half is fixed.

The reason is elementary and now formalized.  If true singleton scalars are independent for the
proposed relation, then any relation-clique intersects the singleton fiber in at most one scalar.
Therefore an at-most-`S` clique cover exists only when the singleton fiber itself has size at most
`S`.  Conversely, if the singleton fiber has size at most `S`, the singleton cover is always a
valid clique cover for any relation.

So the route is exact:

```text
forbidden singleton edges
  -> clique-cover budget <= S  iff  direct singleton-fiber budget <= S.
```

## Lean Surface

`LineListCodewordSingletonRelationCliqueCover.lean` now records both directions:

```lean
scalarRelationCliqueCover_singletons
scalarRelationCliqueCover_card_ge_of_independent
uniformRelationCliqueCoverBudgeted_of_codewordSingletonBudgeted
relationCliqueCoverBudgeted_iff_codewordSingletonBudgeted_of_forbidden
not_relationCliqueCoverBudgeted_iff_exists_singleton_card_gt_of_forbidden
```

The singleton-cover theorem is the positive direction.  It says no graph structure is needed to
obtain a clique cover if the scalar fiber is already small: cover each scalar by `{gamma}`.

The lower-bound theorem is the negative direction.  An independent scalar set meets each clique in
at most one scalar, so every clique cover has at least as many cliques as vertices.  Applied to
singleton witnesses under the forbidden-edge theorem, a smaller clique cover cannot exist.

## Consequence

This does not kill the graph route, but it removes a common ambiguity.  The useful work cannot be
"find a small clique cover" as an independently easier target.  The useful work must be a proof
that the actual singleton fiber has small independence number, small clique cover, or small color
image using algebraic information that also explains why the forbidden-edge theorem is true.

The scanner remains valuable because it returns finite obstructions.  But the collapse theorem
forces the interpretation of those obstructions:

```text
no at-most-S clique cover under forbidden edges
  = an overfull singleton-witness fiber.
```

The next viable tool has to name a genuinely algebraic relation whose edge-forcing proof extracts
a second witness, exceptional pencil, or interpolation obstruction.  Pure finite graph packaging
cannot by itself improve the singleton cap.
