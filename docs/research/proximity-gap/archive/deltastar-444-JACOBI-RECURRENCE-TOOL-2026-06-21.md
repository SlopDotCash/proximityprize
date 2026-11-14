# #444 — The Jacobi / recurrence-coefficient representation of M (a genuinely-new tool)

*Invented + tested this session in response to "invent new tools so new they have no name." Honesty
contract: this RELOCATES the half-power to a sharper object; it does NOT close the prize. Reported honestly.*

---

## The tool

Every named method for `M(μ_n) = max_{b≠0}|η_b|` bounds it through one of two objects, each lossy:
- the **moments** `E_r = Σ_b|η_b|^{2r}` — the `L^{2r}` norm, which over-estimates `M` by *exactly* the
  half-power `K_max^{1/2} = n^{0.385}` (the moment→sup gap is the whole open gap); or
- the **spectrum** `{η_b}` itself — circular.

The new tool uses a third object the campaign never touched: the **three-term recurrence coefficients
`(a_k, b_k)` of the orthogonal polynomials of the empirical η-measure** `μ_η = (1/(q−1))Σ_{b≠0} δ_{η_b}`.
These are the entries of the **Jacobi matrix** `J` (tridiagonal, diagonal `a_k`, off-diagonal `b_k`), and
the key fact is exact:

> **`M = ‖η‖_∞ = ` top of the spectrum of `J`** (the largest support point of `μ_η`), with **no `L^{2r}`
> over-estimate** — the Jacobi matrix *closes the moment→sup conversion exactly*. The truncated top
> eigenvalue `topeig(J_R) ↑ M`, and numerically `topeig(J_R) = M` to machine precision by `R ≈ log p`.

## What the probe found (verified, `/tmp/paley-probes/jacobi_tool.py`, `jacobi_scaling.py`)

1. **The tool is exact:** `topeig(J_R) = M` (ratio `1.000` at `R=28`, n=16 and n=32).
2. **The `b_k` are NOT Hermite — they SATURATE.** For a true Gaussian `N(0,n)` the recurrence is
   `b_k = √(nk)` (Hermite), whose truncated top eigenvalue at `R≈log p` would be exactly `√(2n log p)` =
   the conjecture. The actual `b_k` instead *peak and plateau* (`b_k/√(nk)` falls from `1.0` to `~0.3`),
   reflecting the bounded support `[−n,n]` — the measure is sub-Gaussian, so its recurrence coefficients
   are sub-Hermite.
3. **`M ≈ 2·max_k b_k`** (verified across n=8,16,32,64: `M/(2 max b_k) = 0.97, 1.00, 0.96, 0.99`), with the
   peak at **`k ≈ (log p)/2`** (`kpeak = 4,5,7,7` vs `(log p)/2 = 4.2,5.5,6.9,8.3`).
4. **`b_k` is a SHARPER invariant than the moments.** Across primes at fixed n=16, `2·max b_k` tracks the
   prime-to-prime variation of `M` (`M/(2 max b_k) = 0.94–1.00`), while the shallow energy `E_5/Wick ≈ 0.50`
   is *flat* (prime-independent). So the recurrence coefficients *discriminate* the bad primes that the
   shallow moments cannot — they carry the arithmetic signal the energy averages out.

## Why this is genuinely-new ground — and exactly where it stops

**The relocation (real progress).** The half-power moves from the **exploding** moments `E_r` (`~10^{30}`,
DC-crossing, super-Wick artifacts) to the **bounded, stable** object `max_k b_k` (values `~6–12`, no blow-up).
The conjecture becomes the clean target

> **`max_k b_k ≤ (1/√2)·√(n log p)`**, equivalently `M = 2·max_k b_k ≤ √2·√(n log p)`.

Bounding a *saturating* sequence is a structurally milder problem than bounding an exponentially-growing one,
and the `b_k` (being Hankel-determinant ratios `b_k² = D_{k−1}D_{k+1}/D_k²`) are far more stable than the raw
`E_r`. This is a genuinely-fresh handle, distinct from all ~62 prior angles (it is neither a moment bound nor
a spectral reading nor sum-product).

**Where it stops (honest).** The peak `b_k` sits at `k ≈ (log p)/2`, and `b_k` is a ratio of Hankel
determinants of the moments up to order `~2k ≈ log p`. So `max_k b_k` still *encodes the deep moments* — the
tool **relocates** the half-power into a sharper, bounded object but does **not escape** the deep arithmetic
(the trivial bound `b_k ≤ (support radius)/2 = n/2` gives only `M ≤ n`; the sharp `(1/√2)√(n log p)` needs the
fine sub-Gaussian structure = the wall). The genuinely-new question it poses — *is `max_k b_k` controllable by
a route that the exploding `E_r` obscured?* — is open, and is the sharpest restatement of the wall this tool
produces. The Hankel-ratio / Toda-lattice structure of the `b_k` is the unexplored frontier it opens.

## Status

A genuinely-new tool (the orthogonal-polynomial / recurrence-coefficient representation of the Paley sup-norm),
verified exact, that **relocates the half-power from the exploding moment ladder to the bounded, sharper,
prime-discriminating `max_k b_k`** — real new ground — but does not cross the wall (the peak `b_k` at depth
`log p/2` still carries the deep arithmetic). **NOT closure.** The next concrete step is whether the
Hankel-ratio structure of `b_k` admits a bound the moment ladder cannot give.
