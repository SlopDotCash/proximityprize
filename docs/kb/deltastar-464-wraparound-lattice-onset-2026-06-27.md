# The wraparound onset is a lattice ℓ₁-shortest-vector (2026-06-27)

A novel, exact characterization of the mod-p wraparound onset depth `r₀(p)` as a shortest-vector
problem on an explicit lattice — and the resulting heuristic that **generic primes are good with
exponential margin** (`r₀ ≈ n/4 ≫ ln p`), isolating the floor to a sparse, window-avoidable bad set.
Converges with the independently-found p-adic Norm bound (Workflow-1 `padic-stickelberger` Lemma B).

## The lattice

For `n = 2^μ`, the minimal polynomial of `ζ_n` is `Φ_n(x) = x^{n/2} + 1`, so `ζ^{n/2} = −1` and
`ℤ[ζ_n] ≅ ℤ^{n/2}` with basis `1, ζ, …, ζ^{n/2−1}`. **The `n` roots of unity are exactly the `n`
signed standard basis vectors `±e_0, …, ±e_{n/2−1}`** (since `ζ^{n/2+k} = −ζ^k`). This is the key
simplification: a sum of `2r` roots of unity is a `ℤ^{n/2}`-vector that is a sum of `2r` signed
basis vectors, i.e. any `v` with `‖v‖₁ ≤ 2r` and `‖v‖₁ ≡ 2r (mod 2)`.

Reduction mod `℘` (the degree-1 prime above `p`, `p ≡ 1 mod n`) sends `ζ ↦ ω`, a generator of
`μ_n ⊂ F_p`. So `α = Σ v_i ζ^i` satisfies `℘ | α ⟺ Σ v_i ω^i ≡ 0 (mod p)`. Define the **wraparound
lattice**

```
   L_p = { v ∈ ℤ^{n/2} : Σ_{i} v_i ω^i ≡ 0 (mod p) },   covolume = p,  index p in ℤ^{n/2}.
```

Explicit basis: `(p,0,…,0)` together with `e_i − ω^i e_0` for `i = 1,…,n/2−1`.

## The onset identity (exact, numerically verified)

> **`r₀(p) = ⌈ ℓ₁-min(L_p) / 2 ⌉`**, where `ℓ₁-min(L_p) = min_{0≠v∈L_p} ‖v‖₁`.

A wraparound at depth `r` is a nonzero `v ∈ L_p` writable as `2r` signed basis vectors; the minimum
number of signed basis vectors summing to `v` is exactly `‖v‖₁`, and depth needs `2r ≥ ‖v‖₁` with
matching parity, so the first depth with any wraparound is `⌈ℓ₁-min/2⌉`.

Verified exactly (LLL shortest vector vs FFT-measured onset), `n = 16`:

| p | shortest `v` | `‖v‖₁` | `2r₀` (=‖v‖₁↑even) | onset `r₀` |
|---|---|---|---|---|
| 241 | (−1,−1,1,1,0,1,0,0) | 5 | 6 | 3 |
| 257 | (−2,0,0,1,0,0,0,0) | 3 | 4 | 2 |
| 337 | (−2,1,0,0,1,0,0,0) | 4 | 4 | 2 |
| 353 | (−1,1,−1,1,0,0,1,1) | 6 | 6 | 3 |
| 401,433,449 | (ℓ₁=5) | 5 | 6 | 3 |

Perfect match on every tested prime.

## Why generic primes are good with exponential margin

`L_p` is a random-looking lattice of dimension `d = n/2` and covolume `p`. Minkowski/Gaussian
heuristics give `ℓ₂-min(L_p) ≈ √d · p^{1/d} = √(n/2) · p^{2/n}`. At prize scale `p^{2/n} ≈ 1`
(`p ≈ 2^158`, `n = 2^30`, `p^{2/n} = 2^{316/2^30} ≈ 1.0000002`), so `ℓ₂-min ≈ √(n/2)` — a vector
with `≈ n/2` entries of size `O(1)`, hence `ℓ₁-min ≈ n/2`. Therefore for a **generic** prize prime

```
   r₀ ≈ ℓ₁-min/2 ≈ n/4 ≈ 2^28   ≫   ln p ≈ 110.
```

The prize bound only needs no-wraparound to depth `≈ ln p`; the generic onset exceeds that by a
factor `~2^21`. So **a generic prize prime is good with exponential margin** — the floor holds for
it with enormous room. The only obstruction is an *anomalously short* `ℓ₁-min(L_p)`, i.e. a prime
where `L_p` has an unexpected short vector. These are exactly the **canonical bad primes** the
`land-exhaust` branch enumerates (`p | Res(Φ_n, …)`), and they are sparse (density → 0).

## Convergence with the p-adic Norm bound

Workflow-1's `padic-stickelberger` independently proved **Lemma B**: `α ≠ 0, ℘ | α ⟹ |Norm(α)| ≥ p`.
This is the dual statement: `Norm(α) = ∏_{σ∈Gal} σ(α)`, and a short `α` (house ≤ 2r) has
`|Norm(α)| ≤ (2r)^{φ(n)}`. Lemma B forces `(2r)^{φ(n)} ≥ p`, i.e. `2r ≥ p^{1/φ(n)} = p^{2/n}` — the
*existence* threshold. The lattice view refines this from existence to **count and genericity**:
the Minkowski bound is achieved only by a sparse set of primes; most primes have `ℓ₁-min ≈ n/2`,
far above the `p^{2/n} ≈ 1` existence floor.

## Status

This does **not** close the prize: it does not prove the *specific* prize prime is non-anomalous
(that is the irreducible p-specific crux). But it (i) gives an exact lattice characterization of the
onset, (ii) explains quantitatively why good primes are abundant (generic margin `n/4` vs `ln p`),
(iii) makes the good-prime check a concrete LLL/BKZ computation on `L_p`, and (iv) converges with
the algebraic (Norm) and analytic (BGK) pictures on the same object. The honest residual is
unchanged: prove the prize prime (or a window prime usable by the prize) is lattice-non-anomalous.

## Landable Lean increment

The clean axiom-clean brick is the **Norm bound** (Lemma B): for `α ∈ ℤ[ζ_n]` nonzero with `℘ | α`,
`p ≤ |Norm_{ℚ(ζ_n)/ℚ}(α)|`, via `Int.le_of_dvd` + ideal-norm multiplicativity. The `ℤ[ζ_n] ≅ ℤ^{n/2}`
signed-basis-vector identification of roots is a second clean combinatorial brick.
