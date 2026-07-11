# SYZ25 — the exact combinatorial criterion for cross-core MDS generation (2026-07-11)

Issue #466 / #507. Rate-`1/2` decisive strip `(Johnson ≈ 0.293, 1/3)`.

## Context

SYZ24 (`_SYZ24CrossCoreCompatibility.lean`) reduced the strip's final residual to a single
statement: **generation** `⨆ᵢ Aᵢ = W`, where per core `Cᵢ`,
`Aᵢ := dualAnnihilator (range (evalOnS α k Cᵢ))` is the space of `RS[α,k]` dual codewords supported
inside `Cᵢ`, and `W := A_U` (`U = ⋃ Cᵢ`) is the shortened dual, `finrank W = |U|−k` (SYZ21). SYZ24
proved generation `iff finrank(⨆ Aᵢ) = finrank W` and that it is **not** a support-counting
consequence, but left open *what* generation is combinatorially, and whether the probe's pattern
"over-budget ⟹ generation" is a theorem.

## The exact criterion (duality — proved + probe-validated)

Take perps inside `F^U`. For a core `C`, `Aᶜᗮ = { p : U→F | p|_C ∈ P_{<k}|_C }` (the punctured code
on `C`, zero-extended). Since `(⨆ Aᵢ)ᗮ = ⨅ Aᵢᗮ` and `Wᗮ = P_{<k}|_U`:

> **Generation ⟺ local-to-global polynomial rigidity:** every `p : U→F` that restricts to a
> degree-`<k` polynomial on **each** core `Cᵢ` is the restriction of a **single** degree-`<k`
> polynomial on all of `U`.

Equivalently `⨆ Aᵢ = span{ g_T : T a (k+1)-subset with T ⊆ some Cᵢ }`, `g_T` = min-weight dual
codeword on `T`. The new probe `scripts/probes/probe_syz25_mds_generation.py` **verifies the two
computations of the deficiency `d := (|U|−k) − finrank(⨆ Aᵢ)` agree exactly** on every family
(direct span rank vs. `|U| − dim{local polys}`), and that `d` is a **field-independent** matroid
invariant (identical over `p ∈ {31, 101, 65537}`).

## Main finding: the "over-budget ⟹ generation" corollary is REFUTED

The SYZ24 probe suggested over-budget (`∑(|Cᵢ|−k) ≥ |U|−k`) implies generation. An **exhaustive**
search over all full covers by `(k+1)`-cores at `n ≤ 7` refutes it. Smallest counterexample,
`n=6, k=3` over `GF(7)` (field-independent):

```
C = { {0,1,4,5}, {0,2,3,5}, {1,2,3,4} },   ∑(|Cᵢ|−k) = 3 = |U|−k,   finrank(⨆ Aᵢ) = 2   (d = 1)
```

The three minimum-weight dual lines are **coplanar** in the 3-dim `W`. So generation is *strictly
stronger* than over-budget — a genuine incidence/rigidity fact, not a dimension count. (Exhaustive
census also at `(5,2),(6,2),(7,3),(7,4)`: over-budget families that fail generation exist in every
case except the trivial `n=5`.)

## Sufficient combinatorial condition (probe S1, never fails)

If the cores are orderable so each `Cᵢ` meets the running union `C₁∪…∪C_{i-1}` in `≥ k` points
(**incremental-`≥k`-overlap**), generation holds: a degree-`<k` poly is pinned by `k` points, so
the local polys glue to one global poly. Verified exhaustively (`probe_syz25` S1 ⟹ `d=0`, no
failure). This is the sunflower/chain regime; it does **not** capture all generating families
(random over-budget stacks generate for a subtler joint reason), so it is sufficient, not
necessary — the full over-budget stacks arising from SYZ18 realizability remain the honest input.

## What was proven (`_SYZ25MDSGeneration.lean`, axiom-clean)

Abstract linear algebra over SYZ23's `partialSup` (any field, fin-dim):

1. `generation_iff_dualAnnihilator` — **the exact criterion.** `partialSup A D = W ⟺
   (⨅_{i<D} (A i)ᗮ) = Wᗮ` — the linear-algebra avatar of local-to-global rigidity (via
   `dualAnnihilator_iSup_eq` + `Subspace.dualAnnihilator_inj`). Helper `dualAnnihilator_partialSup`.
2. `generates_of_spanning_generators` / `exists_generator_not_supported_of_not_generates` —
   **generation = every `W`-generator is core-supported.** If `W = span G` and each `g ∈ G` lies in
   `⨆ Aᵢ`, the cores generate `W`; contrapositive extracts the specific uncovered generator `g_T`
   (the `d>0` obstruction).
3. `overbudget_not_imp_generation` — **the corollary is false.** Explicit distinct subspaces
   `A i ≤ W` with `∑ finrank(A i) ≥ finrank W` yet `⨆ Aᵢ ≠ W`: the three coplanar lines
   `⟨e₀⟩,⟨e₁⟩,⟨e₀+e₁⟩` in `W = ℚ³` (all in the plane `{x₂=0}`, so the joint span misses `e₂`).
   Abstract avatar of the `n=6,k=3` RS cover.
4. `syz25Counterexample`, `counterexample_overbudget`, `counterexample_figures`,
   `counterexample_core_sizes` — the concrete RS counterexample cover recorded combinatorially
   (`∑(|Cᵢ|−k) = |U|−k = 3`, cores of size `k+1`), `decide`. The field-independent rank drop
   `d = 1` is the probe fact realized abstractly by (3).

## Honest δ\* verdict

The residual is now **pinned exactly**: cross-core generation is local-to-global polynomial
rigidity (§1) = "every minimum-weight generator of `W` is core-supported" (§2), and it is
**strictly stronger than the over-budget count** — refuted in §3/§4 by an explicit distinct-core
family. So the strip does **not** close from any counting hypothesis. The honest remaining input is
the incidence-geometric fact that the actual over-budget stacks from SYZ18 sunflower realizability
place their cores in generating position (probe: every real GRS stack generates; incremental-`≥k`
families provably do). **Unconditional δ\* status untouched.**

Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`); no `sorry`, no `native_decide`.
```
files: ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ25MDSGeneration.lean
       scripts/probes/probe_syz25_mds_generation.py
```
