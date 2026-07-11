# δ\* / #466 — SYZ32: cluster routing — the SYZ31 crack is matroid-real but stack-vacuous

Date: 2026-07-11
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ32ClusterRouting.lean`
Probe: `scripts/probes/probe_syz32_cluster_routing.py`
Branch: `codex/syz32-cluster-routing` (off `fork/research/proximity-prize` @ f5881e0b3)
Predecessors: `deltastar-466-syz31-set-geometry-2026-07-11.md`,
`deltastar-466-syz29-yield-d4-2026-07-11.md`, `deltastar-466-syz28-d3-coplanar-crack-2026-07-11.md`

SYZ31 refuted the *conjectured* raw two-block cross-intersection floor with the near-duplicate
crack `syz31Crack` (`D=4`, `n=16`, `k=8`, four size-11 cores, matroid rank-deficiency `d=1`
field-independent) and proved the *corrected* floor under a spread-pair hypothesis, asserting the
excluded near-duplicate clusters are "yield-cap-absorbed (SYZ28)". SYZ32 **proves that absorption**
and assembles the case split into the full partition budget.

## The merge-reconciliation verdict: **MATROID-REAL, STACK-VACUOUS**

The rank-deficiency computation (`SYZ31.syz31_two_block_floor_fails`) uses the four cores as
**distinct index sets** — the matroid does not merge them, so `d=1` is genuine and
field-independent. But the **stack-level physics merges the cluster**:

> Two `RS[n,k]` local codewords agreeing on `≥ k` points are **equal** (RS uniqueness / Lagrange).

So on any stack, a near-duplicate cluster whose cores pairwise overlap `≥ k` carries a **single**
local codeword pair `(v₀,v₁)`, hence a single residual pair `(d₀,d₁)`, hence **one** pencil — not
three. The cluster's bad-scalar yield is that of the *merged* core `⋃ cluster`,
`≤ n − |⋃ cluster|`, **not** `∑(n−sᵢ)`: near-duplicate clusters are **yield-degenerate**, not
merely yield-capped. The `D=4` matroid family behaves, on the stack, like the **merged `D=2`
family** `{C₀, C₁∪C₂∪C₃}` (sizes 11, 12).

The rank-deficiency is real in the matroid but the deficient degrees of freedom the lift can excite
collapse to the merged pencils — the counterexample is **matroid-real, stack-vacuous**.

## The lift test (decisive check — probe `probe_syz32_cluster_routing.py`)

1. **matroid** `d=1`, field-independent over `p ∈ {101,1009,65537,10⁶+3,2³¹−1}` (reproduces SYZ31).
2. **merge verified**: on **4000/4000** pencil stacks where ≥2 cluster cores decode, the local
   codewords **coincide** — a single merged pencil, every time.
3. **lift test**: every non-degenerate pencil lift of `syz31Crack` has mutual correlated agreement,
   so the **maximum mca-bad-scalar count is `0`** — the crack produces *no* mca-bad witness at all.
   (Raw un-filtered close-count reaches 18 > n, but those are all correlated-agreement scalars,
   killed by the mca filter — exactly why the filter is load-bearing.) The merged pool
   `(n−s₀)+(n−|⋃cluster|) = 5+4 = 9 ≪ n−1 = 15` (SYZ22 budget) bounds the certified count a
   fortiori. **Strip safe.**

## The assembly (case split, closed)

For any over-budget strict-interior band family, route the cores into blocks:

- **spread blocks** obey the SYZ31 corrected floor (`two_block_floor_of_spread_pair`) ⟹ envelope
  `≥ n−k` ⟹ `d=0` ⟹ generation ⟹ G87 budget;
- **near-duplicate clusters** MERGE (`cluster_codewords_merge`) ⟹ one pencil ⟹ yield
  `≤ n − |⋃ cluster|`; collapsing all clusters gives a merged family of `m` band blocks.

If the merged family has `m ≤ 3` blocks (each band size `≥ s`, `2n < 3s`) the total merged yield is
`∑(n−Uⱼ) ≤ n−1` (`routed_yield_cap_le3`, omega: `3(n−s) ≤ n−1` since `2n < 3s`); `m ≥ 4` merged
blocks necessarily carry a spread pair and route through generation, not the yield sum. Composed
(`routed_bad_le_budget`): **routed certified-bad `≤ n−1`** — the SYZ22 budget, with the clusters
absorbed by the merge, not forbidden.

## Proven verbatim in Lean (axiom-clean: propext/Classical.choice/Quot.sound; no sorry, no native_decide)

- `rs_merge` — RS uniqueness: `degree < k` polys agreeing on `≥ k` points are equal
  (`Polynomial.eq_of_degrees_lt_of_eval_finset_eq`, mathlib Lagrange).
- `cluster_codewords_merge` — two local decodings of the same word on cores overlapping `≥ k` are
  the *same* polynomial (the merge; needs `DecidableEq F` for the intersection).
- `cluster_bad_le_merged_yield` — a merged cluster's bad set `≤ |T|` (one merged pencil; `D=1` case
  of `SYZ29.bad_card_le_pool_of_attribution`).
- `routed_bad_le_sum_yields` — routed bad count `≤ ∑ block yields` (`SYZ29` over the merged blocks).
- `routed_yield_cap_le3` — `m ≤ 3` band merged blocks ⟹ `∑(n−Uⱼ) ≤ n−1` (omega).
- `routed_bad_le_budget` — the assembly: strict-interior over-budget band family, block-attributed
  to `m ≤ 3` merged band blocks ⟹ `#B ≤ n−1`.
- Concrete crack: `syz31Crack_merged_sizes` (merged `D=2`, sizes 11, 12), `syz31Crack_cluster_merges`
  (all cluster overlaps `≥ k`), `syz31Crack_merged_yield_under_budget` (`5+4 ≤ 15`, slack 6) — all
  `decide`, matching the probe's stack-vacuous verdict.

## Scoreboard after SYZ32

1. **Fresh independence-mod-`E`** (lemma 1, SYZ31) — reduced to a private escaping coordinate.
2. **Formula `≤` direction** (lemma 2) — MDS genericity (SYZ25/26); the one substantive open
   analytic residual.
3. **Two-block floor / cluster routing** — **CLOSED as a case split**: spread blocks ⟹ corrected
   floor ⟹ `d=0` ⟹ G87; near-dup clusters **merge** ⟹ yield-degenerate `≤ n−|⋃cluster|` ⟹ routed
   total `≤ n−1` (`routed_bad_le_budget`). The crack is matroid-real, **stack-vacuous** (probe: `0`
   mca-bad). [was: SYZ31 "corrected floor + asserted yield-cap absorption"]

Net: the last set-geometry residual of lemma 3 is **discharged** — not by forbidding the clusters,
but by *routing* them through the RS-uniqueness merge. Only lemma 2 (MDS genericity) remains a
substantive open analytic residual. Unconditional δ\* status untouched; strip not falsified.

## Reuse hooks

- `rs_merge` — generic RS/MDS uniqueness (`deg<k` agreeing on `≥k` ⟹ equal); reuse anywhere a
  near-duplicate overlap should collapse two local codewords.
- `cluster_codewords_merge` — "two local decodings of one word on `≥k`-overlapping supports coincide";
  the mechanism that turns any near-duplicate cluster into a single pencil.
- `routed_bad_le_budget` — the routed-family budget: block-attribute the bad set to `m ≤ 3` merged
  band blocks and read off `#B ≤ n−1`.
- `syz31Crack` (from SYZ31) + this file's probe — the canonical "matroid-real but stack-vacuous"
  worked example; use to sanity-check any deficiency-based falsification attempt before believing it.
