# G250 sponsor row-discrepancy calibration (#466)

G249 formalized the finite row-selection barrier behind the G248 Lu--Zheng--Zheng audit: an
`m × m` Cartesian exceptional set can occupy exactly one complete row at density `1/m`, leaving that
row totally uncontrolled.  G250 records the sponsor-scale arithmetic consumer of that barrier.

The available Cartesian discrepancy is around `2^-15` at both sponsor quotient sizes.  Even granting
the stronger idealized budget `2^-15`, the budget is still far above the row threshold:

- P1 quotient size `m = 2^128 + 192`: a `2^-15` Cartesian budget contains more than `2^113` complete row-lengths.
- P2 quotient size `m = 2^129 + 13`: a `2^-15` Cartesian budget contains more than `2^114` complete row-lengths.

Lean file: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G250SponsorRowDiscrepancyCalibration.lean`.
Theorems include `p1_two_pow_neg15_budget_allows_gt_2pow113_rows`,
`p2_two_pow_neg15_budget_allows_gt_2pow114_rows`, and the P1/P2 instantiations of the G249 one-row
counterexample cardinality.  Axiom audit: arithmetic/cardinality certificates use only the standard
`[propext, Classical.choice, Quot.sound]` stack; no `sorryAx`.

Scope: calibrated route no-go, not a prize closure.  It blocks the specific move “use a global
Cartesian Jacobi-distribution discrepancy as fixed-row weighted control” at sponsor scale.  A real
advance still needs a theorem uniform in the fixed quotient character and stable under the rank
weights, equivalently a full signed sponsor-prime row/covariance estimate for `r = 5, 6`.
