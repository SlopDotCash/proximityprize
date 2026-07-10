# Issue #466 R388: fixed-tail matching rigidity

Date: 2026-07-09

For an eight-slot antipodal matching with at most one edge internal to the variable four slots,
R388 selects a canonical free coordinate. If two matched relation tuples have the same fixed right
half and agree at that coordinate, they agree on every variable slot.

This proves the injectivity mechanism needed for the fixed-reference cell bound: each matching
cell maps injectively to one subgroup value, so its cardinality is at most `|G|`. Combined with
R387, Lam--Leung, and the `7!!=105` matching census, this yields the pending coarse theorem
`rep4(c) <= 105|G|` for nonzero characteristic-zero targets.
