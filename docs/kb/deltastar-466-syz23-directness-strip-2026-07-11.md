# SYZ23 — directness of the anchored-annihilator sum (rate-1/2 decisive strip)

**Issue:** #466 / #507  **Date:** 2026-07-11
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ23DirectnessStrip.lean`
**Probe:** `scripts/probes/probe_syz23_directness_support_leak.py`
**Status:** axiom-clean (propext / Classical.choice / Quot.sound only), no `sorry`, no `native_decide`.

## Context

SYZ22 reduced the rate-1/2 strip `(Johnson, 1/3)` to a single residual: a **lower bound** on the
joint span dimension of an over-budget family's syndrome functionals
(`SuperadditiveUnion.union_span_rank`, still a hypothesis field). SYZ20's `plantable_span_cap`
gives the matching **upper** bound `finrank(span)+1 ≤ 2(n−k)` unconditionally. The strip closes
iff the lower bound `finrank(span) ≥ 2(|U|−k)` can be *proved*.

That lower bound is a **directness** statement about the anchored dual-annihilator subspaces
`Aᵢ := dualAnnihilator(range(evalOnS α k Cᵢ))` = dual codewords supported inside core `Cᵢ`
(`finrank Aᵢ = |Cᵢ|−k`, SYZ21 `shortening_dim`). If `∑ᵢ Aᵢ` is direct, its dimension is
`∑(|Cᵢ|−k)` and the strip closes.

## What SYZ23 proves (verbatim)

1. **Dual distance.** `anchored_dual_small_support_eq_bot/_eq_zero`: a dual codeword of `RS[α,k]`
   supported inside `W` with `|W| ≤ k` is `0` (anchored annihilator = `⊥`). A 3-line corollary
   of SYZ21 `shortening_dim_of_card_le` (finrank 0) + `Submodule.finrank_eq_zero`. Primal route
   to MDS dual distance `k+1`.

2. **Pairwise directness.** `pairwise_direct_of_inter_zero`: `finrank(A⊓B)=0 ⟹
   finrank(A⊔B)=finrank A + finrank B` (modular law `finrank_sup_add_finrank_inf_eq`). Combined
   with (1): two cores meeting in `≤ k` points give a direct pair.

3. **The honest inclusion–exclusion sum lower bound.** `finrank_iSup_ge_sum_sub_overlaps`, for
   any family `A : ℕ → Submodule F V` over a finite-dim `V`:
   `∑_{i<D} finrank(Aᵢ) ≤ finrank(⨆_{i<D}Aᵢ) + ∑_{i<D} finrank(Aᵢ ⊓ ⨆_{j<i}Aⱼ)`,
   i.e. `finrank(⨆Aᵢ) ≥ ∑finrank(Aᵢ) − ∑ overlapᵢ`. Proven by induction from the modular law
   (`partialSup`, `partialSup_succ`). `finrank_iSup_eq_sum_of_direct`: if all overlaps vanish,
   `finrank(⨆) ≥ ∑finrank` (additive budget). **This is the correct accounting**; the residual
   is now sharply localised to bounding the overlap terms `finrank(Aᵢ ⊓ ⨆_{j<i}Aⱼ)`.

4. **The leak (KEY NEGATIVE RESULT).** The natural bound
   `finrank(Aᵢ ⊓ ⨆_{j<i}Aⱼ) ≤ max(0, |Cᵢ ∩ ∪_{j<i}Cⱼ| − k)` (true — the intersection is
   supported in the union support) is **too weak and the LP leaks across the entire strip**:
   - `crudeCost_nested`: a core whose support nests inside the running union (`o = s ≥ k`) has
     support-overlap cost `(s−k) − max(0,s−k) = 0`, at every `k ≤ s`, every rate.
   - `support_accounting_leaks_strip` (decide, n=64,k=32,t=45): the concrete profile
     `leakProfile64` = 2 seed cores `(33,0)` + 63 nested cores `(33,33)` has support-lower-bound
     `2 ≤ n−k−1 = 31` yet certified yield `130 > B = 64`. Nested cores are realizable: spread
     `Cᵢ` (33 pts) over `⌈33/(k−1)⌉ = ⌈33/31⌉ = 2` predecessors each sharing `≤ 31 = k−1`.
   - `nested_tail_cost_zero`: `D` nested cores cost `0` while yield `= 2D → ∞`.

## Verdict

**The corrected accounting does NOT close the strip via support cardinality.** The probe
confirms the leak at every `t ∈ (k, n)` for `n ∈ {32,64}` (see table below). Directness of
`∑ Aᵢ` is a genuine **linear-algebra fact about GRS dual codes** (MDS position of the anchored
annihilators), NOT reducible to counting `|Cᵢ ∩ ∪Cⱼ|`. The overlaps vanish **pairwise** (1)/(2),
but for `D ≥ 3` the union support can exceed `k`, and the *true* overlap
`finrank(Aᵢ ⊓ ⨆Aⱼ)` is strictly smaller than the support bound — that gap is exactly the fact
G87 abstracts as "abstract-H realizability" and SYZ22 packages as `union_span_rank`.

**The leak profile names the next fact:** bound `finrank(Aᵢ ⊓ ⨆_{j<i}Aⱼ)` by the MDS structure
(a dual codeword supported in `Cᵢ` that also lies in the *sum* `⨆_{j<i}Aⱼ` — not merely in a set
supported in `∪Cⱼ` — is heavily constrained by GRS parity), not by support cardinality. This is
the honest residual for the production floor jump `δ* ≥ 1/3`; the unconditional δ* status is
untouched.

## Probe table (support accounting leaks everywhere)

`probe_syz23_directness_support_leak.py`, n=64,k=32: every `t ∈ [33,63]` reports
`LEAK(nested cost-0)` — a size-33 nested core with yield ≥ 1 and 2 predecessors suffices. Same
for n=32,k=16 across `t ∈ [17,31]`. The leak is not a strip-boundary artifact; it is present at
every radius, confirming the support-cardinality route is dead independent of `δ`.

## Production readiness

- **Proven unconditionally & production-general:** dual distance (all `n,k`), pairwise
  directness (abstract), the inclusion–exclusion sum lower bound (abstract, any `D`), the leak
  (general `crudeCost_nested` + concrete `decide`).
- **NOT delivered:** the strip closure. The support-cardinality accounting is proved insufficient;
  the true overlap bound requires GRS/MDS linear algebra beyond support counting. The general-`n`
  knapsack boundary `t ≥ (n+2k+3)/3 ⟹ ≤ n` is moot for this route because the route leaks — no
  finite knapsack over support costs certifies the strip.
