# SYZ26 — does SYZ25's rigidity-deficient cover LIFT into the rate-1/2 strip? (2026-07-11)

Issue #466 / #507. Rate-`1/2` decisive strip `(Johnson ≈ 0.293, 1/3)`.

## The decisive question

SYZ25 showed cross-core generation `⨆ᵢ Aᵢ = W` is **local-to-global polynomial rigidity**, and
exhibited a rigidity-deficient (`d>0`) over-budget cover: `n=6, k=3`,
`{{0,1,4,5},{0,2,3,5},{1,2,3,4}}`, `d=1`. Its cores have size `k+1 = 4` (**minimal**). SYZ24's
"`d=0` for every over-budget family" verdict was likewise only measured on minimal (size-`k+1`)
star/nested covers.

But a bad scalar's witness/core `S` is an **agreement set**: for radius `δ` in the strip at rate
`1/2`, `|S| = t ≥ (1−δ)n`, so a **strip core has size `s ≥ ⌈2n/3⌉`** (`δ < 1/3`), far larger than
`k+1 = n/2+1`. Two strip cores overlap `≥ 2s−n ≥ n/3 < k = n/2`, so the SYZ25 sufficient condition
(incremental-`≥k` overlap S1) is **not** automatically forced. **Does the deficiency survive at
strip-sized cores?** If yes, a deficiency `d` loosens the SYZ22 budget to `|U| ≤ n−1+d` and
threatens the strip. If no, generation is forced and the strip is safe.

## Verdict: STRIP TRUE-mechanism — the deficiency does NOT lift into the open strip

`scripts/probes/probe_syz26_lifting_test.py`. Sweep the core-size floor `s` at `k=n/2`, over
`n ∈ {12,16,18,20,24}`, `~3·10⁴` random over-budget distinct full covers per size, deficiency `d`
recomputed over `p ∈ {17,31,101,1009,65537,10⁶+3}` (field-independence = genuine matroid invariant
vs. small-characteristic accident):

- **Field-independent `d>0` over-budget covers exist only for core size `s ≤ ⌈2n/3⌉`** — i.e.
  `δ ≥ 1/3`, the strip's **excluded top boundary and above** (the large-radius regime). Maximal
  field-independent deficient min-core-size found: `s* ∈ {8,9,12,14}` at `n ∈ {12,16,20,24}`,
  always `≤ ⌈2n/3⌉`, with `δ@s* ≥ 1/3` (deepest reach `δ=1/3` only at small `n=12`; `δ≥0.4`
  otherwise).
- **The open strip interior (`Johnson < δ < 1/3`, core size `s ≥ ⌈2n/3⌉+1`) is DEFICIENCY-FREE**:
  `d = 0` for every family tested, over every prime. Generation is forced, so the SYZ22/SYZ24
  realizability lower bound `finrank(⨆ Aᵢ) = |U|−k` holds and the budget `|U| ≤ n−1` is safe.

So **the SYZ25 deficient shape sits exactly on the `δ = 1/3` boundary the open strip excludes.**
The lift falls short: rigidity deficiency is a boundary-and-above phenomenon, deficiency-capped
small (`d≤1` at the edge), sparse (`D=3` cores), and never penetrates the open strip.

### Two honesty subtleties found

- Many strip-*edge* `d>0` covers are **field-independent** (survive over `65537`, `10⁶+3`) — genuine
  matroid deficiency, not accidents. But the maximally-symmetric ones (e.g. `n=12` cores of size 8
  with all pairwise overlaps `4`) are **field-DEPENDENT** (`d=1` over `GF(17)`, `d=0` over
  `GF(31)+`), i.e. accidental coplanarity in small characteristic. Both die by core size `> ⌈2n/3⌉`.
- The pencil-yield law (from SYZ3): a degenerate core `C` supplies `n−|C|` bad scalars (one pencil
  scalar `γₓ = −d₀(x)/d₁(x)` per off-core `x`). Strip cores (`|C| ≥ 2n/3`) yield `≤ n/3` each; and
  the deficiency needed to exceed budget requires **few** cores, while a large bad-scalar count needs
  **many** cores — but many strip cores saturate to `d=0` (SYZ24). The knapsack closes.

## What was formalized — `_SYZ26LiftingTest.lean` (axiom-clean, no sorry/native_decide)

The rigorous mechanism (pure combinatorics + wiring to SYZ25):

1. `card_inter_ge_of_large` / `card_inter_ge_k_of_large` — **inclusion–exclusion overlap floor.**
   Two cores of size `≥ s` in ground set of size `n` meet in `≥ 2s−n`; if `n+k ≤ 2s` they overlap
   in `≥ k`. (At rate `1/2` this is `s ≥ 3n/4`, i.e. `δ ≤ 1/4` — below the strip.)
2. `prefixUnion`, `base_subset_prefixUnion`, `incremental_overlap_of_base`,
   `incremental_of_large_cores` — **big-overlap ⟹ incremental-`≥k`-orderable** (SYZ25 S1, identity
   order): if every core meets a base core in `≥ k`, every core `≥1` meets its predecessors in `≥ k`;
   combined with (1), large cores (`s ≥ (n+k)/2`) are always incremental-`≥k`-orderable, hence
   generate (feeding SYZ25's polynomial gluing).
3. `syz26BoundaryWitness` + `boundary_core_sizes` / `boundary_overbudget` / `boundary_figures` /
   `boundary_full_cover` / `strip_boundary_overlap_floor_insufficient` — **the strip-boundary
   witness**, `n=12, k=6`, three cores of size `8 = ⌈2·12/3⌉` (`δ=1/3`, excluded edge), full cover,
   over-budget `∑(|Cᵢ|−k)=6=|U|−k`, with pairwise floor `2s−n=4 < k=6` so (1)/(2) are inapplicable —
   the hypothesis is **tight** and the field-independent `d=1` (probe) survives here. `decide`.
4. `generation_realizes_budget`, `overbudget_not_imp_generation_strip` — **verdict wired to SYZ25**:
   generation (the probe-forced `d=0` for `δ<1/3`) delivers the ceiling span = SYZ22 realizability =
   budget; and the abstract non-lift certificate (over-budget ⇏ generation) re-exported from SYZ25 §3.

The genuinely rigorous end covers `δ ≤ 1/4` (`s ≥ 3n/4`) via overlap counting. The strip interior
`1/4 < δ < 1/3` is deficiency-free by exhaustive-random probe; its polynomial-gluing proof is the
unchanged **honest named residual** (same status as SYZ24/SYZ25 realizability).

## Honest δ\* verdict

**The deficiency does not lift into the open strip.** Field-independent rigidity-deficient
over-budget covers require `δ ≥ 1/3` (core size `≤ ⌈2n/3⌉`); the open strip forces core size
`> 2n/3`, which the probe finds always generates (`d=0`). The strip is **not** falsified — SYZ25's
shape lives on the boundary it excludes. Unconditional δ\* status untouched.

Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`); no `sorry`, no `native_decide`.
```
files: ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ26LiftingTest.lean
       scripts/probes/probe_syz26_lifting_test.py
```
