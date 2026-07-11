# Rate-quarter predecessor: the layer-cake budget — exact caps, exhausted counting surface, and the P1 arc retrospective

## Status

Session-closing note of the P1 predecessor pencil arc.  The layered/weighted
budget is computed exactly and formalized; the verdict is that the pure
counting surface cannot close the predecessor budget, and the minimal open
statement is pinned to a concrete 87.5%-saturated packing window.

Formal kernel (pg-iterate ✅ OK 21s, 8 audited theorems axiom-clean —
`three_heavy_twoCover_window` even depends on `[propext]` alone):

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterLayerCakeBudget.lean
```

Probe: `scripts/probes/probe_rate_quarter_p1_layer_cake.py` (exact integer
layer table).

## 1. What is Johnson-listable, precisely

The packed objects are the **pencil pairs** `(w₀, w₁)` — not the directions
alone — packed through their aligned regions
`{i : w₀ i = u₀ i ∧ w₁ i = u₁ i}`.  Pairwise intersections are `< k` by
`alignedSet_inter_card_lt_k` (two pencils agreeing with the stack on a
common `≥ k`-set coincide, via `predecessor_sep`).  The in-tree lemma
applied is `R15Bracket.johnson_core` (exact-diagonal integer Johnson,
`ScaleBracketFull`), through the standard subtracted form.

## 2. The exact layer table (all P1-literal)

```text
Johnson threshold: floor sqrt(N(k-1)) = 536870910
phi (riders) : ladder floor A_phi = ceil((phi*T-N)/(phi-1))
   2 : 111848108      7 : 512637157
   3 : 352321537      8 : 524088272
   4 : 432479347      9 : 532676609   (below threshold)
   5 : 472558252     10 : 539356427   above -> J = 108 pencils
   6 : 496605595     11 : 544700281   above -> J = 35
                     12 : 549072525   above -> J = 22
alignment T-1 = 592794965 -> J = 5    (the classical threshold five)
sub-Johnson pencils (A <= 536870910): riders <= 9, fiber <= 8
   (proved: subJohnson_riders_le_nine; count UNBOUNDED)
```

## 3. The verdict: counting admits over-budget

`counting_admits_three_heavy_overBudget` (proved arithmetic): three pencils
at alignment `T−1` simultaneously satisfy

* the Johnson count (`J(T−1) = 5 ≥ 3`),
* the aligned-region packing (`3(T−1) ≤ N + 3(k−1)`),
* the vote bound at `T−A = 1` (fibers up to `N−T` each),

while carrying `1 + 3(N−T) = 1,442,840,575 > N` bad scalars.  The greedy
heavy-side layer-cake maximum is `2,404,735,416 > 2N` (probe, info only),
and the light side is unbounded in count.  **No uniform counting theorem
assembled from this arc's constraints can prove `#bad ≤ N`.**

## 4. The minimal open statement

`three_heavy_twoCover_window`: a hypothetical three-pencil over-budget
configuration forces the three `~(T−1)`-sized aligned regions to two-cover
`3(T−1) − N = 704,643,071` coordinates within at most
`3(k−1) = 805,306,365` allowed pairwise overlaps — an 87.5%-saturated
packing.  The open question is **RS-algebraic**: can three distinct joint
pairs, all passing through one base witness codeword, agree with a single
stack this densely?  (Compare: at threshold `T` itself the joint list is
`≤ 5` and the interleaved-collapse entry showed `L = 2` already breaks the
naive count — the question lives exactly one lattice step below.)  The
alternative branch remains `PredecessorStructuredFloorResidual`.

## 5. LANE RETROSPECTIVE — the P1 predecessor arc (this session)

Seven rungs, all kernel-checked, all axiom-clean, no `sorry`/`axiom`:

1. `_P1RateQuarterSharedFreshCoordinate` — pencil transport, witness
   incomparability, absorption dichotomy, collinear boost, two-cover bound;
   `SharedFreshTripleFree` residual + consumer; `F₁₁` shared-fresh
   realizability.
2. `_P1RateQuarterNonCollinearTriple` — triple pencil rigidity (overlap
   `≥ k` ⇒ collinear), P1 dichotomy, `3T − 2N < 0`; non-collinear `F₃₇`
   realization at exact P1 shape; residual split.
3. `_P1RateQuarterSharedFreshTripleP1Refuted` — **`SharedFreshTripleFree`
   is FALSE at the literal canonical domain** (μ_16 coset certificate,
   generator-symbolic); per-coordinate charges dead.
4. `_P1RateQuarterPencilCountCharge` — vote partition, uniform rider cap
   `N−T+1`, alignment ladder, ten-rider Johnson crossover (exact at 10),
   fiber partition `#bad ≤ 1 + P(N−T)`, `P ≤ 2` consumer, four-witness
   pigeonhole (`4T > 2N`).
5. `_P1RateQuarterThirdPencilExclusion` — base-triple `< k` overlap
   (characterization); **`BasePencilImageCap` is FALSE at the literal
   canonical domain** (partners-collinear μ_32 certificate, three pencils
   through one base); uniform base-pencil caps dead.
6. `_P1RateQuarterLayerCakeBudget` (this file) — exact layer caps
   (108 / 35 / 22 / 5), sub-Johnson nine-rider cap, and the exhaustion
   verdict.

**Dead** (kernel-refuted at literal P1): per-coordinate escape charges,
collinear-triple freeness, uniform base-pencil caps, and every uniform
counting cap of the arc.

**Standing** (the toolkit, available for the algebraic phase): pencil
transport on `≥ 2T−N` intersections; witness incomparability; absorption
dichotomy; triple rigidity; collinear boost (`⌈(3T−N)/2⌉ ≥ k`); per-pencil
vote caps; alignment ladder; ten-rider crossover; per-fiber weighted cap
`fiber·(T−A) ≤ N−T`; base-triple `< k`; four-witness pigeonhole; the layer
table above.

**Unchanged throughout**: the operational bracket
`3/8 ≤ mcaDeltaStar ≤ 43/96 + 1/(3·2^30) < 1/2` and the predecessor
residual (`PredecessorStructuredFloorResidual` /
`CanonicalLargeBadFourPencilExtraction`).

**Reusable Lean engineering** (see also the per-rung kb notes): kernel
deep-recursion from cross-elaboration `npow`/`SMul` instance defeq at
`ZMod P` (fixes: single-`refine` inlining of big-power polynomials; a
canonical atom function for all big powers; def-equation `rw` +
`simp only [Pi.*]`, never `show`/`rfl` across instance boundaries);
`set` not rewriting later `have`s (omega atom desync); successor-`obtain`
instead of `rw [m = (m−1)+1]`; sum-free card-identity proofs instead of
`sum_comm` under `Fin 2^30`; `pg-iterate` displays only 10 audit lines.

## 6. What this is not

No delta-star change, no refutation of `#bad ≤ N`, no change to the MCA
conjecture's status.  It is the exact and honest closure of the counting
phase of the predecessor branch, with the algebraic target isolated.
