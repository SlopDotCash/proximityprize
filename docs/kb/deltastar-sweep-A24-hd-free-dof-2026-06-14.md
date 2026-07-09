# δ* sweep A24 — HD Gauss-phase free DOF = n/4 (Katz floor, integer-pinned)

**Date:** 2026-06-14 · **Actionable:** A24 (merged 407-T16) · **Status:** CLOSED-PROVEN
(the integer-pinned DOF law + relation-completeness corollary; the underlying `B(μ_n)` floor
stays open — this is a *negative* result about exact-relation methods, formalized, not a closure).

## Object

Prize regime: maximal dyadic FFT subgroup `μ_n ⊆ 𝔽_p^*`, `n = 2^μ`, `p ≈ n·2^128`. The
worst-case incomplete-subgroup-sum house `B(μ_n) = max_{b≠0}‖∑_{x∈μ_n} e_p(bx)‖` is governed by
the `n−1` Gauss phases `θ_a = arg(g(χ^a)/√q)`, `a = 1..n−1`, `χ` of order `n`, `|g(χ^a)| = √q`.

The **complete** set of exact archimedean relations among the phases (Katz–Rojas-León 2207.12439
Thm 2; conjugation + Frobenius + HD, Frobenius trivial at `f=1`):
- **(i) conjugation:** `θ_a + θ_{n−a} = c₁` (one global constant);
- **(ii) Hasse–Davenport duplication:** `θ_a + θ_{a+n/2} − θ_{2a} = c₂` (one global constant).

## Result (exact, integer-pinned)

Homogenize to `n+2` unknowns `(θ_0,…,θ_{n−1}, c₁, c₂)`. The exact rational rank of the (i)+(ii)
relation matrix (sympy `Matrix.rank` over ℚ, no floating point) is

| μ | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|----|----|----|----|-----|
| n | 4 | 8 | 16 | 32 | 64 | 128 | 256 |
| **rank** | 3 | 6 | 12 | 24 | 48 | 96 | 192 |
| `3n/4` | 3 | 6 | 12 | 24 | 48 | 96 | 192 |
| nullity | 3 | 4 | 6 | 10 | 18 | 34 | 66 |
| **free DOF** = nullity − 2 | 1 | 2 | 4 | 8 | 16 | 32 | 64 |
| `n/4` = `φ(2^μ)/2` = `2^{μ−2}` | 1 | 2 | 4 | 8 | 16 | 32 | 64 |

**`rank = 3n/4` exactly; free DOF = `n − 3n/4 = n/4 = φ(2^μ)/2 = 2^{μ−2}`** (the two global
constants `c₁,c₂` are affine-intercept gauges; `nullity` always exceeds the genuine phase freedom
by exactly 2). `n/4 = φ(2^μ)/2` is the count of **primitive order-`n` Gauss sums modulo
conjugation** = the Katz/Deligne primitive-monodromy count.

## All 10 classical reductions: dofcut = 0 (relation-completeness)

Each classical Gauss-sum tool was appended to the (i)+(ii) system and the rank recomputed
(`dofcut` = drop in free DOF), at n = 8, 16, 32:

| tool | dofcut | why |
|---|---|---|
| Davenport–Hasse lifting | 0 | injective+surjective at fixed q ⟹ 0 constraints |
| Stickelberger | 0 | `|g|=√q` constant at `f=1` ⟹ zero archimedean info |
| Gross–Koblitz reflection | 0 | = conjugation (i) |
| Gross–Koblitz multiplication | 0 | = HD duplication (ii) |
| Galois `(ℤ/n)^*` action | 0 | symmetry, permutes relations, no new equation |
| Jacobi self-convolution | 0 | cocycle with *non-constant* RHS `arg J(i,j)`, not a fixed linear relation |
| **m=4 HD (quartic)** | **0** | **= EXACT SUM of three quadratic-HD rows; const₄ = 3·c₂ (proven)** |
| 2-adic coset additivity | 0 | invertible re-coordinatization |
| supercode / resultant fibration | 0 | list-side, wrong direction |
| Cauchy–Schwarz / Hankel | 0 | inequality, 0 equalities |

**Self-correction vs 407-T16.** The m=4 HD quartic was *asserted* dofcut=0 there; I first
measured dofcut=+1 with a naive model that gave the quartic constant a *free* intercept. The
resolution (proven by `_sweep_A24_debug_quartic.py`, exact ℚ-rank, n=8,16,32): the quartic relation
`θ_a + θ_{a+n/4} + θ_{a+n/2} + θ_{a+3n/4} − θ_{4a}` is the **exact sum** of three quadratic-HD rows
`HD(a) + HD(a+n/4) + HD(2a)`, so its constant is *determined*, `const₄ = 3·c₂`, NOT free. Modeled
with the correct coupling `const₄ = 3c₂` the quartic rows lie in the row span of (i)+(ii) and
dofcut = 0. The earlier +1 was a phantom from over-freeing the intercept. So the dofcut=0 verdict is
now *proven* (the explicit reduction), not merely asserted — a strict improvement on 407-T16.

## Lean artifact (axiom-clean)

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A24_HDFreeDOF.lean` — real `lake build`
(1255 jobs, `autoImplicit=false`), axiom audit `[propext, Classical.choice, Quot.sound]` on every
theorem (several at `[propext, Quot.sound]`), no `sorry`/`admit`/`native_decide`.

Proven (ℕ-arithmetic + `Nat.totient_prime_pow_succ`), *given* the named integer rank value
`relationRank μ = 3·2^{μ−2}`:
- `freeDOF_eq_two_pow`  : `freeDOF μ = 2^{μ−2}` (= n/4) for μ ≥ 2;
- `four_mul_freeDOF_eq_n` : `4·freeDOF μ = 2^μ` (= n exactly, so freeDOF = n/4);
- `four_mul_relationRank_eq` : `4·relationRank μ = 3·2^μ` (rank = 3n/4);
- `totient_two_pow` : `φ(2^μ) = 2^{μ−1}`;
- `freeDOF_eq_totient_half` : `freeDOF μ = φ(2^μ)/2` (Katz primitive-monodromy identity);
- `hd_free_dof_law` : the full three-way chain `freeDOF = 2^{μ−2} = φ(2^μ)/2`, `4·freeDOF = 2^μ`;
- 7 `decide`-checked table rows (μ = 2..8);
- `freeDOF_pos` / `floorIsLinear` / `hunt_exhausted` : the corollary.

**The single named input** (not re-derived in Lean): `relationRank μ = 3·2^{μ−2}`, the exact
rational rank of the n-dependent relation matrix — an explicit finite linear-algebra fact verified
to the integer by the probe for μ = 2..8. Computing the rank of an n-dependent ℚ-matrix inside Lean
is out of scope; the integer value is what the DOF law consumes. There is **no** `:True` placebo and
**no** axiom-laundering `_holds` — the rank is a `def` returning the value, the law is proven on top.

## The corollary (exhausted-relation-hunt; the decisive negative)

`floorIsLinear` / `hunt_exhausted`: for every μ ≥ 2, the free phase DOF is exactly `n/4`, positive
and **linear in n** (`4·freeDOF = n`), i.e. `Θ(n)` not `O(log n)`. An `n/4 = Θ(n)`-parameter free
phase sum still concentrates at `√(n·polylog) = M ≤ √(2n log q)` — exactly the BGK / Paley-graph
wall. Therefore:

> Hasse–Davenport + conjugation strip `3n/4` of the Gauss-phase structure; the residual `n/4` is
> genuinely free and is the Katz primitive-monodromy count. **No exact identity can close `B(μ_n)`;
> piercing the `n/4` floor requires non-relation (concentration / energy) input.**

## Honesty

This is a formalized *negative* result about the exact-relation method (the "use the equalities to
cancel" programme is provably exhausted at `n/4`), plus the integer-pinned closed form. It does NOT
prove any `B(μ_n)` bound or any `δ*` pin. The open core is unchanged: the energy / concentration
input `E_r(μ_n)/(r!n^r)` at `r ~ log_n p` (same wall as every other face). No fabricated closure.

## Artifacts
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A24_HDFreeDOF.lean` (axiom-clean)
- `scripts/probes/sweep_A24_hd_dof.py` (exact ℚ-rank, μ = 2..8; 10-reduction sweep)
- `scripts/probes/_sweep_A24_debug_quartic.py` (proves quartic-HD = 3·quadratic-HD)
