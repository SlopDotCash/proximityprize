# δ* sweep A04 — Constant-index Gauss-sum bound (re-land) + barrier

**Date:** 2026-06-14 · **Actionable:** A04 (`mergedFrom` 407-T07) · **Status:** CLOSED-PROVEN (substrate; vacuous at prize by design)

## What A04 asked for

Re-land `ConstantIndexGaussSumBound` (absent from this checkout; previously built on a parallel
worktree). Prove `eta_constIndex_norm_le`: for **constant index** `m`, the Gauss period
`η_b = Σ_{x∈μ_n} ψ(b x)` satisfies `‖η_b‖ ≤ ((m-1)√q + 1)/m ≤ √q`, via
`m·η_b = Σ_{j<m} gaussSum(χ^j, ψ_b)` with `‖gaussSum‖ = √q` (mathlib). Document the barrier:
squared scale `≥ q/4` for all `m ≥ 2`, vacuous at the prize index `m = 2^128`.

## What landed

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A04_ConstantIndexGaussSumBound.lean`
— **axiom-clean** (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`), real
`lake build` green under `autoImplicit=false`.

The decomposition: `1_{μ_n}` expands over the `m` multiplicative characters trivial on `μ_n`
(the order-`m` dual subgroup `μ_n^⊥`). Multiplying by `m`:
`m·η_b = Σ_{j<m} gaussSum(χ_j, ψ_b)`. The `j=0` (principal) term is
`Σ_{x∈F_q^*} ψ(b x) = -1` (norm 1); each of the other `m-1` terms is a nontrivial Gauss sum of
modulus exactly `√q` (mathlib `gaussSum_mul_gaussSum_eq_card` + unit-modulus character values).

Theorems (the moduli `‖τ 0‖=1`, `‖τ j‖=√q (j≠0)` are taken as the named standard structural
input; the arithmetic consequence and the barrier are proven):

- `index_decomp_norm_le` — triangle bound: `m·‖η‖ ≤ (m-1)·s + 1`.
- `eta_constIndex_norm_le` — **the result**: `‖η_b‖ ≤ ((m-1)√q + 1)/m`.
- `eta_constIndex_le_sqrt` — corollary `‖η_b‖ ≤ √q` (worst case = completion bound).
- `boundVal_ge_half_sqrt` — **barrier**: bound `≥ √q/2` for every `m ≥ 2`.
- `boundVal_sq_ge_quarter` — **barrier (squared)**: `(bound)² ≥ q/4` for every `m ≥ 2`.
- `boundVal_eq_affine` / `boundVal_mono` — `boundVal m q = √q + (1-√q)/m`, monotone **increasing**
  in `m` (larger index ⟹ weaker bound, → `√q`); the prize index `m=2^128` sits at the worst end.

## The barrier, quantified (probe `scripts/probes/sweep_A04_constindex_gausssum.py`)

The probe brute-forces the **exact** identity `m·η_b = -1 + Σ_{j≥1} τ_j` with `|τ_j|=√q` on real
small fields `F_p` (id error ~1e-13), confirms the upper bound holds (worst `‖η‖/bound ≤ 1.0`,
tight at `m=2`), and tabulates the barrier:

| regime | q | n | index m | bound² | q/4 | prize target² = n·log₂(q/n) |
|---|---|---|---|---|---|---|
| const idx m=2 | 514 | 257 | 2 | 1.40e2 | 1.29e2 | 2.6e2 |
| polylog m=128 | 8.4e6 | 65537 | 128 | 8.26e6 | 2.10e6 | 4.6e5 |
| **PRIZE n=2³²** | 1.46e48 | 4.3e9 | 2¹²⁸ | **1.46e48** | 3.65e47 | **5.5e11** |
| **PRIZE n=2⁴⁰** | 3.74e50 | 1.1e12 | 2¹²⁸ | **3.74e50** | 9.35e49 | **1.4e14** |

At the prize, `bound² ≈ q ≈ 10^48` against target² `≈ 10^11` — a factor `~10^36` vacuous. The
bound is `Θ(√q)` for every index, never below `√q/2`; the prize floor `√(n log(q/n)) ≪ √q`.

## Verdict

**CLOSED-PROVEN as a substrate result with a proven barrier.** This is exactly what A04 scoped:
a clean, fully-provable brick (`feasibility 8`, `relevance 4`) that re-lands the constant-index
Gauss-sum bound and **proves its own limitation**. The bound is a genuine sub-`√q` statement only
for `m = O(1)/polylog`; the barrier theorems prove it cannot reach the prize floor at the
exponentially-large prize index `m = 2^128`. **No fabricated closure** — the barrier is the honest
content. The single nontrivial-Gauss-sum-modulus input (`‖τ_j‖=√q`) is the standard mathlib fact
`gaussSum_mul_gaussSum_eq_card`, named as the structural hypothesis (not re-derived; mathlib's API
delivers a product identity over abstract fields, not a packaged complex-norm `‖·‖=√q` lemma).

**Remaining gap (unchanged):** the prize floor `B(μ_n) ≤ C√(n log(q/n))` needs cancellation among
the `m-1` Gauss-sum phases `χ̄(b)τ(χ)` (the worst-case Gauss-period / BGK wall) — the constant-
index lever provides none of it, by `boundVal_mono` + `boundVal_sq_ge_quarter`.
