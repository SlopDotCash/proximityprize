# Retention mapping: G326 incidence bounds — 2026-09-06

The full `scripts/probes/g326_overdet_incidence_max_stronger_decoupling.py`
replay passes. Retain this exact-integer cross-check of the incidence maximum
formula `2m³ - 2m² + 1`. This adds one artifact to the original unreferenced
cohort: 41 of 92 reviewed, with 51 remaining.

The two equivalent formulas agree at all 49 integers from 2 through 50.
The four tight bounds have coefficients 4, 12, 24, 40 and lower endpoints
2, 3, 4, 5 respectively; their endpoint margins are all 1. Their tested
ranges contain 49, 48, 47, 46 cells. Each cell passes the strict inequality,
non-strict bulk inequality, and factored-margin equality. The separate 8m
bound passes all 48 cells from 3 through 50, with endpoint margin 13.

Corrected two descriptions in the probe: the double-budget bound is not
tight, and the margin is cubic in m for fixed d, not quadratic. The two
formulas are algebraically equivalent evaluations, not independent
implementations of the underlying incidence model. Integer computations
are unchanged; the summary now describes cubic growth correctly.

Source inspection maps the 12m, 24m, and 40m bounds to
`overdetIncidenceMax_gt_12m`, `overdetIncidenceMax_gt_24m`, and
`overdetIncidenceMax_gt_40m` in `OverdetIncidenceMaxClosedFormExt.lean`.
Those proofs were inspected but not recompiled in this audit. The finite
replay does not prove the universal statements or close the Proximity Prize.
The companion JSON records the source hash, complete output, and scope.
