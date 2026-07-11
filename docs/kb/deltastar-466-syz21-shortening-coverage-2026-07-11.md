# SYZ21: MDS shortening dimension proven in-tree + combined-coverage LP audit (2026-07-11)

Status: **Lean landed, axiom-clean** (`Frontier/_SYZ21ShorteningAndCoverage.lean`) + arithmetic
probe (`scripts/probes/probe_syz21_combined_coverage_lp.py`). Two parts, both answering questions
SYZ20 left open. Issue #466 / #507. Tag SYZ21.

## Part A — the MDS shortening dimension is now proven in-tree (discharges SYZ20's bridge)

SYZ20 packaged, as the unproven hypothesis `SuperadditiveUnion.union_span_rank`, the MDS-duality
fact: *the dual codewords of `RS[α,k]` supported inside a coordinate set `U` have dimension
`max(0, |U|−k)`.* SYZ21 **proves this fully in-tree** from the primal RS vanishing-set machinery
`ArkLib.CS25.finrank_ker_evalOnS` (Lagrange interpolation + Vandermonde, already in
`ArkLib/Data/CodingTheory/RSVanishingDim.lean`) plus the standard dual pairing on `U → F`.

Key reformulation (avoids ever defining the GRS dual code, which is **not** in-tree — RS's
`checkMatrix` is defined but its dual-correctness is unproven): the dual codewords supported in
`U` are exactly the functionals on the punctured-code space `U → F` that annihilate the punctured
RS code `range (evalOnS α k U) ≤ (U → F)`, i.e. `(range (evalOnS α k U)).dualAnnihilator`. Then
`Subspace.finrank_add_finrank_dualAnnihilator_eq` gives

  `finrank (dualAnnihilator (range evalOnS)) = |U| − finrank (range (evalOnS α k U))`.

The punctured-code dimension is the MDS information-set fact `finrank (range (evalOnS α k U)) =
min(k, |U|)`:
- `|U| ≤ k`: `evalOnS` is surjective (`evalOnS_surjective`, Lagrange), dim `= |U|`;
- `k ≤ |U|`: `evalOnS` is injective — a degree-`<k` poly vanishing on any `k`-subset `S ⊆ U` is
  `0` (`finrank_ker_evalOnS S = k − k = 0 ⇒ ker = ⊥`), so dim `= k`.

Hence dual-support dim `= |U| − min(k,|U|) = max(0,|U|−k)`. **Fully proven, axiom-clean.**

Residual to a *fully concrete* `SuperadditiveUnion` instance (still open, honestly): the
identification of G87's syndrome-pair functionals with this punctured-code annihilator (the
"abstract-H" bridge), and the pair-doubling `2(|U|−k)`, plus sunflower realizability on one stack
(SYZ18). The **dimension count** — the mathematical core of the bridge — is no longer a
hypothesis.

## Part B — combined-coverage audit: the honest adversarial optimum (the decisive question)

**The question.** SYZ20's `mergeOpt` maximises the certified bad-scalar count over **pure
single-core-size** profiles: `⌊(n−k)/(s−k+1)⌋ · yield(s)`. But a bad scalar can instead carry a
*distinct non-degenerate witness* `(S,c)` — its own G87 block of `t−k` γ-weighted functionals in
the `2(n−k)`-dim syndrome-pair pool (G86 caps such independent blocks at `⌊(2(n−k)−1)/(t−k)⌋`,
= 5 at `n=64, t=43`). Does the joint-rank/union argument, which SYZ20 applied only to the
degenerate-**core** part, still close once these independent blocks compete for the **same** rank
pool?

**The resolution.** Independent-block scalars are **not a separate uncaptured category** — an
independent block is simply the large-`s` end (`s = t−1, t`, `yield = n−t+1, n−t`) of the *same*
item menu, costing `s−(k−1)` in the shared sunflower union. So the honest adversarial optimum is
the full **integer knapsack** over the union budget `n−k` (capacity), items `s ∈ [k+1, n−1]`,
cost `s−(k−1)`, value `yield(s)`. This is `≥ mergeOpt` (single-item is a feasible knapsack point).
Computed exactly (`knapOpt`, decidable list-DP; probe `probe_syz21_combined_coverage_lp.py`):

```
 n=64,k=32, survival budget B=n=64, pair-pool 2(n-k)=64
 t   delta    zone      mergeOpt  knapsack  indep-only  B    verdict
 40  0.3750   above1/3   100       100        7         64   LEAK
 41  0.3594   above1/3    72        79        7         64   LEAK
 42  0.3438   above1/3    69        72        6         64   LEAK
 43  0.3281   STRIP-top   48        59        5         64   CLOSES
 44  0.3125   STRIP       42        50        5         64   CLOSES
 45  0.2969   STRIP       40        46        4         64   CLOSES
```
Scanned `n ∈ {16,32,64,128,256}` (probe): in **every** case the knapsack crosses `B = n`
**exactly at the strip top** (`δ = 1/3 − 1/(3n)`): the last `δ>1/3` row LEAKs, the first STRIP
row CLOSES. Strip-top knapsack/B ratio ≈ 0.92 (n=64: 59/64; n=128: 116/128; n=256: 235/256) —
bounded away from 1, so the closure is robust, not marginal.

### Verdict (the honest headline)

**The SYZ20 coverage claim SURVIVES the adversarial audit — there is NO mixed-profile leak — but
`mergeOpt` is a single-item UNDER-COUNT of the true optimum.** Precisely:

- **No leak.** Mixed profiles (degenerate cores + independent non-degenerate blocks) are all
  captured by the shared-pool knapsack. Independent blocks are far too rank-inefficient
  (`1/(t−k)` bad-scalars per pair-dim vs `up to ~1.0` for near-degenerate cores; `n−t ≥ 2` in the
  strip makes cores strictly dominant), so at the optimum the adversary uses `≤ 5` of them and
  the strip closes.
- **Correction to SYZ20.** The true adversarial optimum is the knapsack `59, 50, 46` (n=64),
  strictly above SYZ20's advertised single-item `48, 42, 40`. Both are `< 64`; the honest margin
  is thinner (`0.92·n`, not `0.75·n`). The crossover with `B` remains **exactly** at `δ = 1/3`,
  so the qualitative strip-closure boundary is unchanged.

**Classification of the strip theorem:** **complete-CONDITIONAL**, not gapped. Conditional on the
same bridge SYZ20 named (now with Part A's dimension count discharged, leaving only the
G87-abstract-H functional identification + SYZ18 sunflower realizability), the degenerate/syzygy
channel provably starves throughout `(Johnson, 1/3)` — and this now holds against the *full*
mixed-profile adversary, not just pure-core profiles. Unconditional δ* bracket unchanged:
`3/8 ≤ δ* ≤ 43/96+ε`.

## Formal results — `Frontier/_SYZ21ShorteningAndCoverage.lean` (axiom-clean)

`propext, Classical.choice, Quot.sound` only (the `decide` lemmas: `propext` only). No `sorry`,
no `axiom`, no `native_decide`.

Part A:
- `punctureDim_of_card_le` / `punctureDim_of_le_card` — `finrank (range (evalOnS α k U)) = |U|`
  (resp. `= k`) for `|U| ≤ k` (resp. `k ≤ |U|`).
- `shortening_dim_of_le_card` — `k ≤ |U| ⇒ finrank (dualAnnihilator (range evalOnS)) = |U| − k`.
- `shortening_dim_of_card_le` — `|U| ≤ k ⇒ … = 0`.
- `shortening_dim` — combined: `= |U| − k` (`= max(0,|U|−k)`), the value SYZ20 consumes.

Part B:
- `yieldS` / `coreCost` / `knapStep` / `knapTable` / `knapOpt` — the shared-pool integer
  knapsack (decidable list-DP).
- `knap_closes_strip_n64` (`= 59, 50, 46`) / `knap_closes_strip_n64_lt` (`< 64`) — strip closure.
- `knap_kills_above_third_n64` (`> 64` at `t=40,41,42`) — crossover pinned at the strip top.
- `knap_closes_strip_n32` — `n=32` agrees.

## Cross-references
- SYZ20 (what SYZ21 discharges/audits): `docs/kb/deltastar-466-syz20-joint-rank-superadditive-2026-07-11.md`.
- Primal RS machinery used in Part A: `ArkLib/Data/CodingTheory/RSVanishingDim.lean`
  (`evalOnS`, `evalOnS_surjective`, `finrank_ker_evalOnS`); `ReedSolomon.lean`; `Vandermonde.lean`.
- SYZ18 (sunflower realizability, remaining residual): `Frontier/_SYZ18PairJointSelfExclusion.lean`.
- G87 bridge (functional identification, remaining residual): `Frontier/_G87McaEventSyndromeBridge.lean`.
- Probe: `scripts/probes/probe_syz21_combined_coverage_lp.py` (knapsack n=16…256 + strip-top pin).
- Issue #466 / #507. Tag SYZ21.
