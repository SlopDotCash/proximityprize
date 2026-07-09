## Deep-extremality addendum: the KKH26 orbit is EXACTLY extremal at its ceiling band (240-pair sweep + perturbation + hill-climb)

Follow-up to the two-regime census (`probe_deep_extremal_search.py`). The correct deep metric is **#distinct pinned scalars** (raw alignable-supply is gamed by `u₀ ∈ code` lines, which align every set but pin only `γ = 0`).

At `(n=16, k=3, μ=3, m=2)`, band `a = 6` (the KKH26 ceiling band), full character sweep, all 240 pairs:

| rank | pairs | deep #bad |
|---|---|---|
| **1 (max)** | **(6,4), (4,6), (14,12), (12,14)** — the KKH26 construction + its inversion images | **40** |
| 2 | (10,12), (10,4), (8,14), (8,6) | 25 |
| 3 | (14,8), (12,10), (12,6), (6,12) | 24 |

103/240 pairs have some deep mass (even-frequency structures factoring through the squaring quotient); the **maximum is exactly the KKH26 orbit**. 120 random perturbations of the construction and 8 graded hill-climbs (near-alignment credit for gradient) never beat it — random starts collapse to 0, KKH26 starts return to the 56-supply/40-scalar optimum.

**Combined verdict of the census programme at this scale:** the deep alignment census is maximized by the KKH26 family, its supply terminates exactly at `1 − r/2^μ`, and the boundary-band order (where KKH26 is near-minimal) reverses at depth. The conjectured pin value is what the deep census computes, with the extremizer identified. The open core is unchanged but now maximally concrete: *prove the deep alignment census is KKH26-dominated* — a statement with exact, field-independent, machine-checked small-scale instances on record.
