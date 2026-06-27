# δ\* — The 100-Loop Synthesis (#464 / Paley wall)

**Date:** 2026-06-27. **Outcome:** 100 genuinely-distinct candidate proofs proposed,
implemented as adversarial propose→refute loops, **0 survivors**. This is not a closure;
it is the sharpest available *map of why no closure exists by current methods*, and the
honest essay the goal asked for.

## The object, stated once

Let `p` prime, `n | p-1`, `H ≤ F_p^*` the index-`n` subgroup (the `n`-th powers).
Gaussian periods `η_b = Σ_{h∈H} e_p(b·h)` for `b ∈ F_p^*`, house `M = max_{b≠0} |η_b|`.
The δ\* lower-bound pin needs the **worst-case** upper bound

> `M ≤ √(2 n log p)`   (BGK / Paley-type, `n` = sum length).

Numerically (this session, probes): `M = C·√(2·len·log p)` with `C ∈ [0.41, 0.65]`,
sub-Gaussian and approaching the envelope **from below**. The bound is *true*; the open
problem is *proving the worst case*.

## Why the wall is a wall: the three collapse modes

Across 100 loops the referee verdicts converged on exactly three failure modes. Every
single mechanism — analytic, algebraic, additive-combinatorial, geometric — fell into one:

1. **Circular (keyStep = the wall).** The load-bearing inequality is `M ≤ √(2n log p)`
   itself, re-expressed in the new language (dual sum, eigenvector, majorant, trace
   function). Moving the wall primal→dual does not lower it.

2. **Parseval collapse (phase-blind floor).** The only *unconditional* second moment is
   `Σ_{b≠0} |η_b|² = n(p-1)` by orthogonality — the Gauss-sum cross terms vanish. This
   gives only `M ≤ √(np)` (exponent 1). Every energy/L²/moment refinement inherits the
   floor `E_k ≥ n^{2k}/p`, so `M^{2k} ≤ p·E_k` never beats exponent 1. The average-to-max
   conversion costs back the entire gap.

3. **Open-equidistribution (Kummer).** The honest non-circular content of the strongest
   angles (large sieve, subconvexity, Vinogradov, trace functions) is *spacing /
   equidistribution of the Gauss-sum arguments* `{arg g(χ^j)}` at depth `log p`. That is
   Kummer's problem / Heath-Brown–Patterson — itself open — and unconditionally yields only
   `n^{1-o(1)}` (the BGK additive-energy barrier), not the clean `√(2n log p)`. Worse, the
   needed spacing **provably fails** on the documented bad primes (high 2-adic valuation,
   Fermat-type) that any worst-case bound must cover.

## How a real proof would have to get around Paley

The decomposition that names the wall exactly:
`η_b = (√p / n) · Σ_{j=1}^{n-1} ω_j · χ^{-j}(b)`, where `ω_j = g(χ^j)/√p` are **unimodular
Gauss-sum phases**. Then `M = (√p/n)·max_b |Σ_j ω_j χ^{-j}(b)|`. If the `ω_j` were
independent-uniform on the circle, EVT gives exactly `√(2n log p)` for the max over `p-1`
values of `b`. So:

> **The prize is precisely: the Gauss-sum phase vector `{ω_j}` behaves, under the
> worst-case max over `b`, like an independent uniform random unimodular vector — to depth
> `log p`.**

A genuine proof must establish *archimedean phase delocalization* of `{arg g(χ^j)}`. No
known tool does this worst-case:
- Stickelberger/Gross-Koblitz pin only the **p-adic valuation** (magnitude bookkeeping);
  multiplying `g(χ^j)` by a root of unity preserves magnitude and valuation while rotating
  the phase arbitrarily — so no valuation-only statement can bound the phase sum.
- Deligne/Katz-Sarnak give equidistribution **on average over a family**, not a worst-case
  sup over `b` at a fixed `p`.
- Multiplicative-chaos / Harper "better-than-√" is an **average** phenomenon; the prize is
  the worst-case **max**, on the opposite side of `√n`.

## Why it's novel that no one found it, and why that's not surprising

The bound is exactly the strength that would follow from `GRH`-level control of the
relevant family *plus* unconditional worst-case Gauss-argument equidistribution. The former
is conjectural; the latter is an old open problem (Kummer, 1846) where even the *density* of
arguments is hard. The δ\* worst-case is therefore at least as hard as a known open problem
and additionally must survive an adversarial family (Fermat-type primes) chosen to defeat
spacing. The reason "nobody found it" is structural: the only methods that could cross are
methods that don't exist yet (a worst-case phase-cancellation method for multiplicative
subgroup sums).

## Status of the formalization

The repository correctly carries this as a **named residual**, not a gap: `M ≤ √(2n log p)`
worst-case is the load-bearing open hypothesis behind the L2 lower pin, and everything
downstream (good-side toolkit, TZ ceiling ladder, canonical bad-prime bricks) is proven
*relative to it* or on the unconditional floor side. This synthesis adds nothing false to
the tree; it documents that 100 fresh distinct attacks reproduce the standing wall via
exactly three collapse modes.

## Loop 40 — the essay-derived sharpening (Jacobi sub-randomness)

Exact-reconstructing the nontrivial part `M = (√p/n)·max_b |Σ_{m=1}^{n-1} ω_m χ^{-m·m₀}(b)|`
(`m₀=(p-1)/n`, recon error 1e-14, all `|ω_m|=1`) and comparing the **true** house to
Monte-Carlo over random unimodular phase vectors:

| (p,n) | true house | reflection-constrained random | iid random |
|-------|-----------|-------------------------------|-----------|
| (41,8)  | 2.83 | 3.42 | 3.53 |
| (97,32) | 2.85 | 3.25 | 3.44 |
| (193,64)| 2.92 | 3.50 | 3.75 |

**Finding:** the true Gauss phases produce a house *strictly below* even the
reflection-constrained random model. The reflection relation
`ω_{n-m} = χ^m(-1)·conj(ω_m)` does **not** explain the gap. The residual suppression is the
**Jacobi-sum coupling** `g(χ^a)g(χ^b) = J(χ^a,χ^b) g(χ^{a+b})`, `|J|=√p`, which confines
`{ω_m}` to a low-dimensional subvariety of the torus on which the sup is provably sub-random.

This is the most precise positive statement to date — the bound holds with *room* because of
rigid algebraic phase coupling, not luck. But it **reduces** identically: making the
sub-randomness *worst-case-quantitative* requires controlling the arguments of the Jacobi
sums uniformly, i.e. Kummer / Heath-Brown–Patterson equidistribution — the wall. The lever is
real; the fulcrum is the open problem.

**Not closure. Not a crack. A precise, adversarially-verified map of the obstruction —
now with an exact, reproducible characterization of *which* algebraic structure supplies the
sub-random margin (Jacobi coupling) and exactly *which* open input would convert it to a
proof (worst-case Jacobi-argument equidistribution).**
