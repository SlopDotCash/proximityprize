# δ\* #407 — cosh-MGF root-free reduction at the saddle: same anomaly wall as the moments (A03)

**Date** 2026-06-14 · **Actionable** A03 (merged 407-T15) · **Type** numerical-probe + analysis
· **Status** PARTIAL (both cancellations re-verified exact; the saddle bound is the moment
method in disguise and inherits the identical char-0↔char-p anomaly wall; not attackable by a
non-moment convexity argument as found)

**Artifacts**
- `scripts/probes/sweep_A03_cosh_mgf.py` (+ `_A03_results.txt`) — full sweep.
- `scripts/probes/_A03_validity.py` (+ `_A03_validity.txt`) — the decisive y_valid-vs-y_opt test.

---

## 0. The object

The dyadic proximity-gap prize reduces to the worst Gauss-period sup-norm
`B(μ_n) = max_{b≠0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)`, with conjectured floor
`B ≤ √(2 n log(q/n)) = √(2 n log m)`, `m = (p−1)/n`.

407-T15 reported two **exact** cancellations:

- **(C1) √p factors out.** `τ(χ^j)=√p·u_j`, `|u_j|=1`, so `M(n)=√(n/m)·R`,
  `R = max_b|Σ_{j=1}^{m−1} χ̄^j(b) u_j|`. Floor `M ≤ √(2n log m) ⟺ R ≤ √(2m log m)` — no √p.
- **(C2) the max becomes a cosh-MGF (no 2r-th root).** Summing `Σ_b|η_b|^{2r}=p·E_r` against
  `y^{2r}/(2r)!`:  **`Σ_{b∈F_p} cosh(|η_b|·y) = p·I₀(2y)^{n/2}`** (char-0, exact). One-term
  bound `M ≤ min_y (1/y)·arccosh(p·I₀(2y)^{n/2})`; saddle `y* = √(2 log p / n)` claimed to give
  `M ≤ √(2n·log 2p)·(1+o(1))` = the floor, "with no 2r-th root, no √p, no max."

A03 charter: re-verify both; compare the MGF-at-saddle bound vs the moment-method bound vs the
true `B` across n=8..256 / many primes; locate where it fails at structured primes (n=16,
p=786433); decide whether the root-free form is attackable by a non-moment (convexity /
log-concavity) argument the raw moments are not.

## 1. Both cancellations re-verified EXACT (Part 1)

| n | p | C1 (Parseval) rel.err | C2 (cosh @y=0.15) lhs/rhs |
|---|---|---|---|
| 8 | 257 | 1.1e-16 | 1.00000001 |
| 16 | 65537 | 1.3e-15 | 1.00000003 |
| 16 | 786433 | 8.9e-16 | 1.00000000 |
| 32 | 1048609 | 1.1e-15 | 1.00000414 |
| 8 | 3209 | 3.3e-16 | 1.00000000 |

(C1) is literally `Σ_{b≠0}|η_b|²=pn−n²` (Parseval), machine-exact. (C2) is exact at small `y`
(char-0 regime). **Both confirmed.**

## 2. The cosh identity (C2) FAILS at deep y — the same anomaly, in the conjugate variable

The char-0 RHS `p·I₀(2y)^{n/2}` is only the true `Σ_b cosh(|η_b|y)` **below the char-p
anomaly**. Pushing `y` up exposes the break (lhs/rhs):

| (n,p) β | y=0.6 | y=1.0 | y=1.5 | y=2.0 |
|---|---|---|---|---|
| (16,65537) β=4 | 1.001 | 1.044 | 1.459 | 2.933 |
| (16,786433) β=4.9 | 1.000 | 1.0001 | 1.006 | 1.054 |
| (32,1048609) β=4 | **1.502** | **71.6** | **3226** | **41953** |

The structured prime **n=16, p=786433** (high 2-adic valuation, β≈4.9) keeps the identity valid
deeper in `y` — the *exact same* "structured primes delay the anomaly" phenomenon seen in the
moment variable `r` (memory `arklib-389-deep-moment-wall`). The cosh-MGF did NOT relocate the
wall; it re-expressed it as a divergence in `y` instead of in `r`.

## 3. The decisive test: the saddle lies OUTSIDE the identity's validity region (FICTION)

For each prize-shaped `(n,p)` measure `y_valid` = largest `y` with char-0 cosh ratio ≤ 1.02,
and `y_opt` = the minimizer of `(1/y)·arccosh(p·I₀(2y)^{n/2})` (`_A03_validity.py`):

| n | β | p | y_valid | y_opt | verdict |
|---|---|---|---|---|---|
| 16 | 3 | 4129 | 0.54 | 2.35 | **OUTSIDE (4.4×)** |
| 16 | 4 | 65617 | 0.99 | 4.38 | **OUTSIDE (4.4×)** |
| 32 | 3 | 32801 | 0.28 | 1.20 | **OUTSIDE (4.3×)** |
| 32 | 4 | 1048609 | 0.42 | 1.66 | **OUTSIDE (4.0×)** |
| 64 | 3 | 262337 | 0.15 | 0.77 | **OUTSIDE (5.1×)** |

**In every prize-shaped instance the bound's optimal `y` (and the theoretical saddle
`y*=√(2 log p/n)`) sits a factor 4–5× above `y_valid`.** The number `min_y (1/y)·arccosh(
p·I₀(2y)^{n/2})` that "equals the floor" is computed by evaluating the char-0 identity in a
region where it is false by orders of magnitude (the (32,1048609) row above: off by 71× at
y=1.0, 4·10⁴ at y=2.0). So the char-0 saddle bound is a **fiction in the regime it is read off**:
it is *not* a valid upper bound on `B`. It coincides with the floor only because the *false*
char-0 RHS is being used.

## 4. The honest char-p one-term bound saturates at the trivial `n`

Using the *true* (char-p) `Σ_b cosh(|η_b|y)` gives the only legitimate one-term bound
`mgf_p = min_y (1/y)·arccosh(Σ_b cosh(|η_b|y))`. The sweep (Part 2/3):

| n | p (β=4) | trueB | floor | **mgf_p** | mom_p (char-p moments) |
|---|---|---|---|---|---|
| 16 | 65617 | 13.30 | 16.32 | **16.00** | 13.79 |
| 32 | 1048609 | 22.98 | 25.80 | **32.00** | 24.01 |
| 64 | (β=2) 4289 | 19.21 | 23.20 | **64.00** | 20.24 |

`mgf_p` pins to **exactly `n`** because the sum runs over **all** `b∈F_p`, including `b=0` where
`η_0=n`, so `Σ_b cosh(|η_b|y) ≥ cosh(ny)` ⟹ `(1/y)arccosh(·) ≥ n`. A *single-term*
(non-moment) reading of the full-`F_p` cosh sum can therefore never drop below `n`, which is
useless (the target is `√(2n log m) ≪ n`). The b=0 mass is exactly what the moment method
*subtracts* (`Σ_{b≠0}|η_b|^{2r}=pE_r−n^{2r}`); the cosh-MGF as stated keeps it.

**`mom_p` (the honest char-p moment bound, optimized over r) is the genuinely useful one** —
it beats the floor (B/floor 0.68–0.96 across the sweep). The cosh-MGF, read honestly, is
strictly *worse* than the moments, not better.

## 5. Verdict on the A03 question: is the root-free saddle form non-moment-attackable?

**No (as found).** The cosh-MGF is the *generating function of the very same even moments*
`E_r`: `cosh(|η|y)=Σ_r |η|^{2r} y^{2r}/(2r)!`. Consequently:

1. The char-0 saddle "floor" uses `p·I₀(2y)^{n/2}` = the char-0 `E_r` packed into a series; it
   is the **moment method's char-0 baseline rebound**, valid only to depth `r ≍ y√n`, i.e. only
   for `y ≲ y_valid`. The saddle `y*` is past that (§3), so it reproduces the **identical
   anomaly wall** the moment route hit (the char-p energy `E_r^{F_p}` exceeds `E_r^{char0}` for
   `r ≳ 2 log_n p` ⟺ `y ≳ y_valid`).
2. The honest char-p version (§4) is the moment bound *minus the subtraction of the b=0 term*,
   hence weaker.

The hoped-for advantage — that the MGF is "log-concave / convex" in a way the discrete moment
sequence is not — does **not** materialize: `arccosh(p·I₀(2y)^{n/2})` is convex and smooth, but
its value is only an upper bound on `B` where the underlying identity holds, and that is exactly
the moment-validity window. Convexity in `y` buys nothing the convexity of `r ↦ log E_r` (the
moment route) does not already buy; the binding constraint is *validity of the char-0 surrogate*,
not the smoothness of the optimization. **No non-moment handle was found.** This confirms (does
not refute) the consolidation's verdict that all faces reduce to the same `E_r^{F_p}` deep-moment
wall, and removes the cosh-MGF from the list of "unexplored escape routes."

## 6. What WOULD be needed (the residual, stated honestly)

A genuine escape would require a *direct* upper bound on `Σ_{b≠0} cosh(|η_b|y)` (b=0 excluded)
**at `y ≈ y*`** that does not pass through the char-0 surrogate `p·I₀(2y)^{n/2}` — i.e. a
char-p control of the cosh sum at the saddle. That is precisely the open object
`Σ_{b≠0}|η_b|^{2r} ≤ q(2r−1)‼n^r` at `r ≍ log m` (the `GaussianEnergyBound` Prop), re-expressed.
The cosh repackaging is exact and pretty, but **it leaves the open input verbatim where it was.**

## 7. One-line

The two 407-T15 cancellations are exact and confirmed; the saddle bound only "equals the floor"
because it evaluates the char-0 cosh identity 4–5× past its validity radius in `y`; the honest
char-p one-term bound saturates at the trivial `n`; the root-free form is the moment method in
the conjugate variable and inherits the identical char-0↔char-p anomaly wall. **PARTIAL — no
closure, no new attack surface; cosh-MGF de-listed as an escape route.**
