# δ* exact pins (#444 RQ): the n=16 table on the Fermat prime F₄=65537 — 2026-06-15

**Type:** closed related-quantity increment (exact δ* table). **Status:** LANDED, axiom-clean
(`propext, Classical.choice, Quot.sound`; real `lake build` EXIT 0, 3063 jobs).

**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/DeltaStarTableN16Fermat.lean`

## What was banked

The first consolidated exact table of the **MCA threshold `mcaDeltaStar`** (the prize quantity,
NOT a list-size crossover) at `n = 16`, on the canonical smooth testbed
`μ_16 = ⟨4⟩ ⊆ F_p^×`, `p = 65537 = 2^16 + 1` (the Fermat prime F₄), for all four prize rates.
Each row instantiates the granularity ladder (`mcaDeltaStar_rs_eq_granularity`,
`GranularityLadderRS.lean`) at the **maximal** band index `j` for which the ladder closes
(`3(j−1)+k ≤ n` and `j+1+k ≤ n`), giving an exact *maximal-window* pin
`mcaDeltaStar(RS[F_p, μ_16, k]) ε* = j/16` for every `ε* ∈ [j/p, (j+1)/p)`.

| ρ    | k | j(max) | δ* = j/16 | ε*-window           | theorem                  |
|------|---|--------|-----------|---------------------|--------------------------|
| 1/2  | 8 | 3      | 3/16      | [3/65537, 4/65537)  | `deltaStar_rho_half`     |
| 1/4  | 4 | 5      | 5/16      | [5/65537, 6/65537)  | `deltaStar_rho_quarter`  |
| 1/8  | 2 | 5      | 5/16      | [5/65537, 6/65537)  | `deltaStar_rho_eighth`   |
| 1/16 | 1 | 6      | 6/16=3/8  | [6/65537, 7/65537)  | `deltaStar_rho_sixteenth`|

Capstone: `deltaStar_table_n16_F65537` bundles all four. Domain is a genuine smooth subgroup:
`dom : Fin 16 ↪ ZMod 65537` enumerating `{4^0,…,4^15}`, with injectivity and
`(dom i)^16 = 1` both `decide`-proven (`dom_pow16_eq_one`). `p − 1 = 2^16` ⟹ `μ_16` is a
proper, thin (`16 ≪ 65537`) subgroup; `β = log_16 65537 = 4` sits exactly on the Burgess
barrier defining the prize regime `β ∈ [4,5]`.

## Why this is NEW (no duplication)

Surveyed all in-tree exact δ* results before building:
- **`mcaDeltaStar` exact pins** existed only as SINGLE instances: `DeltaStarExactPinF5`
  (n=4, ρ=1/2, δ*=1/4), `DeltaStarSecondPinF17{,Maximal}` (n=8, ρ=1/2, δ*=1/4),
  `DeltaStarPinMu8F4129` (n=8, ρ=1/4, δ*=5/8 — the one beyond-Johnson pin).
- The only existing *table* `DeltaStarTableSmoothInstances` certifies a **different quantity**:
  list-size crossovers `listSize a* ≤ B < listSize(a*−1)`, not the threshold `mcaDeltaStar`.

So this file is the first: (1) consolidated `mcaDeltaStar` table; (2) δ* pin at n=16;
(3) δ* covering all four prize rates on one field; (4) δ* on a μ_16 subgroup domain; (5) δ*
on the Fermat prime F₄. The granularity engine is reused verbatim — the contribution is the
new instantiation + the smooth-domain construction + the consolidated capstone.

## Honest scope — what this is NOT

The granularity ladder pins δ* only **below** the window. At n=16 it reaches δ* ≤ 6/16 = 0.375,
while the Johnson radius `1−√ρ` for these rates is `0.293, 0.5, 0.646, 0.75`. Every pin here is
therefore **strictly sub-Johnson** (the unconditional regime). This is the exact closed form
*below* the prize window; the **window-interior pin (the open core) is untouched**. The result
is bound to a fixed finite shape, not the asymptotic `n=2^30, ε*=2^{−128}` prize family.

It does NOT bear on the open core (BGK/Paley sup-norm wall `M(n) ≤ C√(n log m)`): the ladder is
a pure spike-floor / forced-universal-witness counting argument, orthogonal to the character-sum
wall. It is a clean, decidable, prize-faithful *data-point increment* to the exact δ* table — its
value is as ground truth / sanity anchor, not as progress on the wall.

## Reusable mechanics (cost real debugging time)

- **`norm_num` for `Nat.Prime 65537` needs `import Mathlib.Tactic.NormNum.Prime`.** The
  import chain via `GranularityLadderRS` does NOT transitively bring the prime norm_num
  extension; without it `by norm_num` silently leaves `⊢ Nat.Prime 65537` as an unsolved goal
  that surfaces as `sorryAx` in the axiom audit. `decide` on `Nat.Prime 65537` hits max
  recursion depth — use `norm_num` + the explicit import.
- **`decide` on `Function.Injective (![...] : Fin 16 → ZMod 65537)` WORKS** (~31s) and is
  axiom-clean. Same for `∀ i, (dom i)^16 = 1`. The large modulus is fine for these finite checks.
- **Timing gotcha:** these `decide` checks take ~30s; a `timeout 200` wrapper around
  `lake env lean` was silently killing the run on this box — run with the raw timing harness
  (`START=$(date +%s); OUT=$(lake env lean F); ...`) to see the real ~31s elapse.
- After the ladder wrapper + `rw [Fintype.card_fin] at h`, the hypothesis is literally the goal
  `mcaDeltaStar … = (j:ℝ≥0)/16` — close with `exact h` (no `convert … <;> norm_num`, which
  warns "norm_num does nothing").

## Pointers

- Engine: `mcaDeltaStar_rs_eq_granularity`, `mcaDeltaStar_eq_granularity`
  (`UniversalStaircaseCollapse.lean`).
- Predecessor single pins: `DeltaStarExactPinF5.lean`, `DeltaStarSecondPinF17Maximal.lean`,
  `DeltaStarPinMu8F4129.lean`.
- The list-size (different-quantity) table: `DeltaStarTableSmoothInstances.lean`.
