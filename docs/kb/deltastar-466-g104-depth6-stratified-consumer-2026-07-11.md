# Issue #466 G104: depth six via the stratified-L² primitive-concentration ladder

Date: 2026-07-11 (landed `c829905dc`)

## Statement

Depth six of the padded-collision lane closes from two named hypotheses at the **uniform
Stepanov level** `4·n^{2/3} = 2^22`:

- `primQuadCount S x ≤ 2^22` pointwise (primitive quadruple concentration — no antipodal
  pair, no zero-sum triple), and
- `zeroTripleCount S ≤ 2^22` (total ordered zero-sum triples),

at `S.card = 2^30`, with kernel margin `2^{1.955}`
(`Frontier/_G104DepthSixStratifiedConsumer.lean`, 15 axiom-clean declarations,
`production_depth6_of_primitive_quad`).  Notably depth six needs **no pair-concentration
hypothesis**: the crude `pairCount ≤ n` suffices inside the recursion.

## The corrected ladder mechanism (why this file matters beyond one rung)

At depth ≥ 6 the naive `J_s ≤ maxN_s·n^s` chain is LOSSY: the antipodal tower concentrates
`maxN₆` at the few targets with positive pair count and overshoots the budget by `2^5`.  The
consumer instead runs a **stratified L² split**: `sextCount = P + A + B` along the quad strata
(primitive / antipodal / zero-triple), the exact weighted square
`4(P+A+B)² ≤ 5P² + 40A² + 40B²` (defect `(P−4A−4B)² + 20(A−B)²`), and the stratum squares
recurse through LOWER-depth equal-sum masses (`ΣA² ≤ 36n²·J₄` with `J₄` bounded by the
depth-4 rung).  The ladder is inductive in depth — each rung consumes the previous rungs'
masses.  Machine-checked stratum bounds: `antipQuadCount ≤ 6·n·pairCount` (six position-pair
injections), `ztQuadCount ≤ 4·zeroTripleCount` (four position-triple injections), exact
partition `quadCount = prim + zt + antip`.

## Context and empirics

- G102: pair statistics provably insufficient at depth ≥ 5 (extremal witness).
- G103: depth-5 consumer from centered triple concentration.
- G104 (this): depth-6 consumer; probe measures primitive `M₄` of real `μ_n` at
  `4!·{1,1,1,1,3,7}` — O(1)-ish, `2^{19}` headroom below the hypothesis level.
- Threshold band `n^{0.73..0.87}` stable across all depths 5..110
  (`probe_466_g104_primitive_concentration_ladder.py`): the uniform PrimitiveConcentration
  family is the pinned input interface of the whole lane.  With G87W's Stepanov discharge of
  the depth-4 pair hypothesis (concurrent, `4b4011f48`), producing Stepanov analogs for the
  primitive k-sum concentrations (k ≥ 3, target `n^{3/4}`-level) is the natural next
  certificate programme — strictly weaker than square-root cancellation at every order.

## Honest scope

Consumer only; both hypotheses are named external inputs, unproved in Lean.  Depths ≥ 7 need
the general-k strata bookkeeping (same mechanism, more strata); the all-depth assembly and
the ON-BGK core remain open.
