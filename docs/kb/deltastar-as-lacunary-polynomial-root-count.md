# The prize δ* as a lacunary-polynomial root count over roots of unity — a clean classical reduction (#407)

A clean analytic reformulation of the far-line list-decoding radius (the object the numerics cannot resolve,
per `CRITICAL-numerics-cannot-distinguish-johnson-from-floor.md`). It connects the prize to classical
sparse-polynomial / vanishing-sums-of-roots-of-unity theory — the right *analytic* attack surface.

## The proposed reduction (pointwise exact; the max-root-count reading is false — see correction)

The far-line monomial list-decoding radius was proposed to be
> *(Superseded, see the correction below.)* **s*(n,k) = max number of roots in μ_n of a polynomial `P(x) = x^a + γ·x^b − c(x)`** (`deg c < k`, any
> `γ ∈ F_q`, `a,b ∈ [k,n)`) — i.e. the max μ_n-root-count of a polynomial with **support `{a,b} ∪ {0,…,k−1}`**
> (a **(k+2)-term lacunary polynomial**).

The pointwise equivalence is exact: agreement of the far line `x^a+γx^b` with a degree-<k codeword on a set
`S ⊆ μ_n` is precisely `P` vanishing on `S`. **But the identification `δ* = 1 − s*/n` with `s*` the unrestricted
maximum above is false (audit T164).**

**An allowed binomial beats the table.** Take `c = 0`, `γ = −1`, `b ∈ [k, n/2)` and `a = b + n/2`, which is
admissible whenever `k < n/2`. Then `P(x) = x^b(x^{n/2} − 1)` vanishes on the `n/2` square roots of unity in
`μ_n`, so the unrestricted maximum is **at least `n/2`**. More generally it is at least `max gcd(a−b, n)` over
admissible `a, b`. Concretely, `x^{12} − x^4 = x^4(x^8−1)` has 8 roots in `μ_16`, which exceeds the tabulated
`s*(16,4)=7`; likewise `x^{10}−x^2` gives 8 `> 5` at `(16,2)` and `x^{18}−x^6` gives 12 `> 11` at `(24,6)`. So the
tabulated `s*` values are **not** this maximum. They are the engine's binding sizes for the far-line incidence
threshold: the first agreement size at which the number of bad scalars `γ` drops to the budget (cf.
`deltastar-exact-asymptotic-formula-and-budget.md`, where `δ*(μ_16,k=4) = 9/16` is a budget crossing). That is a
count-over-`γ` threshold, not a single-polynomial root count. Moreover, since `n/2 > √(kn)` whenever `k < n/4`,
the unrestricted maximum sits above the Johnson value for such rates, for trivial binomial reasons. The
"Johnson vs floor" question is therefore **not** a question about this maximum. Any lacunary reformulation must
(i) count scalars `γ` against the budget instead of maximizing over a single `γ`, and/or (ii) exclude such
degenerate binomial directions (e.g. `gcd(a−b, n)` large) explicitly.

## Verified data (engine)

Columns: `s*` is the engine's budget-crossing binding size (not the unrestricted max root count; see above).

| n | k | s* | terms (k+2) | √(kn) |
|---|---|---|---|---|
| 16 | 4 | 7 | 6 | 8.0 |
| 16 | 2 | 5 | 4 | 5.7 |
| 24 | 6 | 11 | 8 | 12.0 |
| 24 | 12 | 16 | 14 | 17.0 |

Note `s* > k+2` (more roots than terms) — possible because **factors of `x^n−1` are themselves sparse**
(cyclotomic polynomials), so a lacunary `P` can be divisible by a high-degree sparse factor of `x^n−1`.

## The connection to classical theory (the analytic handoff)

The open question — does `s* = √(kn)` (Johnson) or `s* = k + Θ(n/log n)` (floor) asymptotically — is now a
**lacunary-polynomial root-count** problem:
- **Vanishing-sums-of-roots-of-unity:** `P(ζ)=0` for `ζ ∈ μ_n` ⟺ a weighted vanishing sum of n-th roots of unity.
  Controlled by **Mann's theorem** and **Conway–Jones** (minimal vanishing sums) — already in the campaign's
  toolkit for the char-p side.
- **Sparse polynomial root bounds:** the number of roots of unity of a `t`-sparse polynomial — **Bombieri–Zannier**,
  **Filaseta–Lenstra** (sparse factors of `x^n−1`), **Lenstra** (cyclotomic factors). These bound the unrestricted
  maximal root count, which is **not** the tabulated `s*` (see the correction above).
- This is the **GG25 curve-decodability / list-size object** (the in-tree prize engine) re-expressed as a lacunary
  root count — a cleaner, more classical statement of the same open core.

## Why this is the right form

- It is **finite and exact** (no char-p, no probability) — a pure question about roots of a structured polynomial.
- It connects to **citable classical theory** (Mann/Conway–Jones/Bombieri–Zannier/Filaseta–Lenstra) — the
  literature the prize "reduces to."
- *(Corrected.)* The Johnson-vs-floor distinction is **not** whether a `(k+2)`-sparse polynomial of this shape can
  have `k + Θ(n/log n)` roots in μ_n or is capped at `√(kn)`. The binomial `x^b(x^{n/2}−1)` already has `n/2`
  roots. A faithful lacunary form must count the scalars `γ` (with multiplicity over subsets) against the budget,
  or exclude degenerate directions.

## Reading list (added to PAPERS_NEEDED)

- Bombieri–Zannier, "Algebraic points on subvarieties of G_m^n" (sparse polynomial / torsion points).
- Filaseta–Lenstra / Lenstra, sparse factors of x^n−1, cyclotomic factors of lacunary polynomials.
- Conway–Jones, "Trigonometric Diophantine equations" (minimal vanishing sums of roots of unity).
- Mann, "On linear relations between roots of unity" (1965).
- (Connect to GG25 curve-decodability: the list-size of RS for 2-sparse-spectrum words.)

## Status

A pointwise-exact translation of far-line agreement into vanishing of a `(k+2)`-term lacunary polynomial on
`μ_n`, which connects to classical sparse-polynomial / vanishing-sum theory. **The claimed reduction of δ* to the
unrestricted maximal root count is false** (audit T164): admissible binomials give at least `n/2` roots, exceeding
both the tabulated `s*` and `√(kn)` for `k < n/4`. The prize δ* is a budget-crossing count over `γ`. Turning it
into a lacunary root-count question needs a counting formulation or an explicit exclusion of degenerate
directions, and that is not done here. NOT a closure.
