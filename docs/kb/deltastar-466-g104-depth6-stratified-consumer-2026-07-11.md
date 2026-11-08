# Issue #466 G104: depth six via the stratified-L² primitive-concentration ladder

Date: 2026-07-11 (landed `c829905dc`)

## Statement

Depth six of the padded-collision lane closes from two named hypotheses of different kinds:

- `primQuadCount S x ≤ 2^22` pointwise (primitive quadruple concentration — no antipodal
  pair, no zero-sum triple), a fiber cap at the Stepanov level `4·n^{2/3}`, and
- `zeroTripleCount S ≤ 2^53` (TOTAL ordered zero-sum triples),

at `S.card = 2^30`, with kernel margin `≈ 2^{0.37}`
(`Frontier/_G104DepthSixStratifiedConsumer.lean`, `production_depth6_of_primitive_quad`;
the intermediate `four_mul_mass_le` is parametric in `Z₃`).  **Correction (2026-10 audit,
CW-B05-01):** the original statement used `Z₃ ≤ 2^22` and called both hypotheses "at the
uniform Stepanov level".  A total count and a pointwise cap are not comparable that way, and
for a multiplicative subgroup `Z₃` is a multiple of `|S| = 2^30` (scaling acts freely on
zero-sum triples; `_G105ZeroTripleQuantizationFence.lean`), so `Z₃ ≤ 2^22` forced `Z₃ = 0`.
The `Z₃` term is far from binding: the kernel closes up to `log₂ Z₃ ≈ 53.26` and fails at
`2^54`.  Notably depth six needs **no pair-concentration
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
- The scoping archive `_out_466_g104_ladder_scoping.txt` proposed one uniform
  PrimitiveConcentration cap `4·n^{2/3}` for every arity `3..108` as the input interface of the
  whole lane, with a threshold band `n^{0.73..0.87}`.  **Correction (2026-10-28 audit, T117):**
  that uniform raw cap is **false** at production scale — at arity 8 an averaging argument
  (a dilate of `μ_n` puts `≥ 2^27` points in `{1,…,(p−1)/8}`, all of whose ordered 8-tuples are
  primitive) forces some target to have `≥ 2^58` primitive representations, and at arity 11
  `scripts/probes/probe_466_g104_primitive_concentration_factorial_no_go.py` exhibits
  `11! = 39916800` primitive tuples with one sum.  The band also used a `C(110,s)²` envelope,
  while the formal decoder uses `descFactorial(110,s)² = (s!)²·C(110,s)²`.  So the archive is a
  retired proposal, not an input interface.  A feasible deep-depth producer must keep the
  inevitable uniform population term, use an actually centered quantity, or be
  depth-dependent, and must be wired to the exact decoder normalization; none is formulated.
  This does not affect the depth-six consumer here or its explicit primitive-quad input.

## Honest scope

Consumer only; both hypotheses are named external inputs, unproved in Lean.  Depths ≥ 7 need
the general-k strata bookkeeping (same mechanism, more strata); the all-depth assembly and
the ON-BGK core remain open.
