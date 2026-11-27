# Domain-Independent `2n + 2` Barrier at the Quarter-Rate Johnson Sign Pivot

## Summary

At quarter rate (`k = d + 1`, `n = 4(d + 1)`, `d ≥ 3`), the Hamming error count
`e = 2d + 3 = n/2 + 1` (agreement threshold `t = n - e = 2d + 1`) is the exact
finite-length Johnson sign pivot:

- `(n - e)^2 = (2d + 1)^2 = 4d^2 + 4d + 1 = n · d + 1 > n · d`, so `e / n < 1 - √(d / n)`
  lies strictly **below** the finite-length Johnson radius;
- `(n - (e + 1))^2 = 4d^2 < n · d`, so `(e + 1) / n` crosses strictly **above** it.

At production scale `n = 2^30`, `k = 2^28`, `d = 2^28 - 1`, this pivot is `e = 536,870,913`,
where the second-prime 128-bit security budget is `B₂ = 2^31 = 2n = 2,147,483,648`.

`ArkLib/Research/ProximityGap/Frontier/QuarterPivotDomainIndependentBarrier.lean` proves
**100% unconditionally in Lean 4** (zero `sorry`, zero custom axioms, zero written-geometry
gaps) that **no domain-independent theorem** can establish 128-bit MCA safety at the
quarter-rate Johnson sign pivot `e = 536,870,913`:

1. **`quarter_pivot_failure_of_domain` & `universal_quarter_pivot_failure`:** For every
   `d ≥ 3` and every finite field `F` containing a primitive `(d - 1)`-th root of unity `ω`
   and nonzero `u₀, v₀` with `1, u₀^(d-1), v₀^(d-1)` pairwise distinct and
   `Choose(8d + 10, 2) ≤ |F|`, there exists an injective evaluation domain
   `dom : Fin (4(d + 1)) ↪ F` on which a 4-head pencil achieves
   `(8d + 10) / |F| = (2n + 2) / |F| ≤ epsMCA` at `δ = (2d + 3) / (4(d + 1))` for every
   positive interleaving width.
2. **`production_quarter_pivot_domain_independent_barrier`:** Over the Lucas-certified
   159-bit smooth prize-shaped prime
   `Q = 730750818869487914369817427303088068110372044801`
   (`Q - 1 = 2^92 · 5^2 · 7 · 13 · 17 · 73 · 557 · 262657 · 357283`, satisfying
   `Q / 2^128 = 2^31 = 2n` and `2^30 ∣ (Q - 1)`), there exists `dom : Fin (2^30) ↪ ZMod Q`
   such that for every positive interleaving width:
   - `(2,147,483,650 : ℝ≥0∞) / Q ≤ epsMCA (RS(dom, 2^28)^⋈ width) (536,870,913 / 2^30)`,
   - `1 / 2^128 < epsMCA` (strictly exceeding the 128-bit security tolerance by 2 bad scalars),
   - `mcaDeltaStar ≤ 536,870,913 / 2^30 < 1 - √((2^28 - 1) / 2^30)` (strictly below the
     finite-length Johnson radius).
3. **`smooth_mu16_f1009_quarter_pivot_failure`:** At `d = 3, n = 16, k = 4, e = 9` in
   `ZMod 1009`, because `(d - 1) = 2 ∣ 16`, the exact same 3-coset construction embeds
   directly onto the **literal smooth subgroup** `μ₁₆ ⊂ ZMod 1009` (`domMu16 = powDomain zeta16`),
   proving `34 / 1009 ≤ epsMCA` (`34 > 32 = 2n`) strictly below `1 - √(3/16)` for every
   positive interleaving width.

## Zero-Search Algebraic Construction

Let `r₀ = u₀^(d-1)`, `s₀ = v₀^(d-1)`, and `λ = (s₀ - 1) / (s₀ - r₀)` (so `λ ∉ {0, 1}`).
Define two degree-`(d - 1)` polynomials:

- `g₁₂(X) = X^(d-1) - 1`, whose root set is the coset `B₁₂ = ⟨ω⟩` (size `d - 1`),
- `g₁₃(X) = λ (X^(d-1) - r₀)`, whose root set is `B₁₃ = u₀ ⟨ω⟩` (size `d - 1`).

Then:
- `g₁₃(X) - g₁₂(X) = (λ - 1)(X^(d-1) - s₀)` has root set `B₂₃ = v₀ ⟨ω⟩` (size `d - 1`),
- `g₁₃(X) - λ g₁₂(X) = λ(1 - r₀) ≠ 0` is a **nonzero constant polynomial** (zero roots in `F`).

Partition `dom` into 7 disjoint parts: `B₁₂, B₁₃, B₂₃` (each size `d - 1`), three pairs
`E₁, E₂, E₃` (each size `2`), and `B_rem` (size `d + 1`), all disjoint from `B₁₂ ∪ B₁₃ ∪ B₂₃`,
totalling `3(d - 1) + 6 + (d + 1) = 4d + 4 = n`.

Take 4 polynomial heads `(p_h, q_h, r_h)` of degree `≤ d < k`:

| Head `h` | `(p_h, q_h, r_h)` | Core (size `2d`) | Owns received word on |
| :--- | :--- | :--- | :--- |
| `0` | `(0, 0, 0)` | `B₁₂ ∪ B₁₃ ∪ E₁` | `B₁₂ ∪ B₁₃ ∪ E₁` |
| `1` | `(0, X g₁₂, g₁₂)` | `B₁₂ ∪ B₂₃ ∪ E₂` | `B₂₃ ∪ E₂` |
| `2` | `(0, X g₁₃, g₁₃)` | `B₁₃ ∪ B₂₃ ∪ E₃` | `E₃` |
| `3` | `(g₁₂, λ X g₁₂, λ g₁₂)` | `B₁₂ ∪ B_rem` | `B_rem` |

Because `q_h = X r_h` for all four heads and `v(x) = x w(x)` on every site `x`, every fresh
event `(h, x)` satisfies `key(h, x)₁ = -x`, immediately pinning the site `x` by injectivity
of `dom`. At a fixed site `x`:
- On `B₁₂` (`d - 1` sites): head `2` is fresh (`1` event/site → `d - 1`).
- On `B₁₃, B₂₃, E₁, E₂, E₃` (`2d + 4` sites): one collinear head gives `key₀ = 0` while head `3`
  gives `key₀ ≠ 0` (`2` events/site → `4d + 8`).
- On `B_rem` (`d + 1` sites): heads `0, 1, 2` give `key₀ = g₁₂(x) / (r_h(x) - λ g₁₂(x))` with
  pairwise distinct denominators because `r₀(x), r₁(x), r₂(x)` are pairwise distinct outside
  `B₁₂ ∪ B₁₃ ∪ B₂₃` (`3` events/site → `3d + 3`).

Total distinct fresh events: `(d - 1) + (4d + 8) + (3d + 3) = 8d + 10 = 2n + 2`, handed
directly to `LinearPencilFreshLabels.mass_of_distinct_fresh_labels`.

## Honest Scope and Relationship to `PrizeShapePrimeP30Second`

This theorem refutes **domain-independent** safety at `e = 536,870,913` (`n = 2^30`, `k = 2^28`,
budget `B₂ = 2^31 = 2n`), even when restricted to smooth `2^30`-friendly 159-bit primes `Q`
with `Q / 2^128 = 2^31`. It does **not** directly refute safety on the specific designated
second-prime smooth subgroup `H = μ_{2^30} ⊂ ZMod PrizeShapePrimeP30Second.P`: there,
`d - 1 = 2^28 - 2 = 2 · (2^27 - 1)` does not divide `2^30`, so the three `μ_{d-1}`-cosets
cannot lie inside `μ_{2^30}` (in contrast to `n = 16, d = 3`, where `d - 1 = 2 ∣ 16` allows
the literal `μ₁₆` embedding in `smooth_mu16_f1009_quarter_pivot_failure`).

Consequently, any proof that the designated second-prime quarter-rate MCA boundary lies above
Johnson (i.e. safe at `536,870,913`) must genuinely exploit the multiplicative structure of
`H = μ_{2^30}` (such as obstructing split degree-`d` pencils on `μ_{2^30}`), rather than
treating `dom` as an arbitrary `2^30`-element subset of `F`.

## Verification

- Lean module: `ArkLib/Research/ProximityGap/Frontier/QuarterPivotDomainIndependentBarrier.lean`
- Independent verification probe: `scripts/probes/probe_quarter_pivot_domain_barrier.py`
  (verifies `n = 16` on literal `μ₁₆ ⊂ F₁₀₀₉` by brute force including explicit separating
  `(a, b) = (1, 5)` and `max_correlated_agree = 6 < 7 = t`, plus `n = 32, 64, 128`, plus the
  full production prime `Q` certificate).
