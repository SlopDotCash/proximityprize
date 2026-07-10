# Issue #466 R389: fixed-tail matching-cell bound

Date: 2026-07-09

R389 turns R388's rigidity into the exact cardinality statement needed for the fourfold
representation theorem. For a fixed reference four-tuple and a perfect matching with at most one
variable-variable edge, the matching cell injects into the subgroup through its canonical free
coordinate. Therefore

```text
card(matchingCell) <= card(G).
```

Together with R387 and the `7!!=105` perfect matchings, this leaves only the Lam--Leung cover and
reference-fiber packaging before `rep4(c) <= 105*card(G)` is fully assembled in characteristic
zero.
