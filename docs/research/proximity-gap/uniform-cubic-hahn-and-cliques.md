# Uniform Cubic Hahn Smooth-List Bracket Upgrades, Boosted Boundary Shells, and Forced Saturated Cliques

This note documents Milestone 2 of the Grand List Decoding Challenge lower-bound track,
building directly on `CubicHahnJohnson.lean` and `HintBoundaryShell.lean`.

All theorems reported below are **Lean-checked** (zero `sorry`, zero custom axioms;
`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`) and independently confirmed
in exact rational arithmetic by
`scripts/probes/probe_uniform_cubic_hahn_and_cliques.py`.

---

## 1. Uniform-in-Length Cubic Hahn Bounds & `SmoothListRankBracket` Upgrades

**Lean module:** `ArkLib/Research/ProximityGap/Frontier/UniformCubicHahnBracket.lean`

### 1.1 Exact Central-Moment Sum-of-Squares Identities & Universal `Θ(√n)` Strip

Writing $d = t^2/n + \delta$, $r_0 = t^2/n - \sigma$, and $V = t^2(n - t)^2 / (n^2(n - 1))$,
`cubicC2_central`, `cubicC1_central`, and `cubicC0_central` establish three exact
identities valid for all $n \ge 5$:

- `cubicC2 n t (t²/n + δ) (t²/n - σ) = 6(n - 2t)² / (n(n - 4)) + 2(2σ - δ)`
- `cubicC1 n t (t²/n + δ) (t²/n - σ) = ((2(n² + 10n - 12)t(n-t) - 6n²(n-1))² + 2n³(n-1)(n-2)²(n-3)) / (2n²(n-1)(n-2)(n-3)(n² + 10n - 12)) + V + (2σ - δ)(n - 2t)²/(n(n - 2)) + σ(σ - 2δ)`
- `cubicC0 n t (t²/n + δ) (t²/n - σ) = t²(n - t)²(n - 2t)² / (n³(n - 1)(n - 2)) + (2σ - δ) V - δ σ²`

This immediately yields:
- **`cubic_hahn_exact_sqrt_barrier`**: finite list bound across the entire exact Cubic Hahn
  `√V` super-Johnson barrier `(k - 1) - t²/n < σ ≤ √V`.
- **`cubic_hahn_sqrt_strip`**: for **ANY** field `F`, **ANY** injective domain `D : I ↪ F`
  (`n ≥ 5`), **ANY** dimension `k`, **ANY** interleaving width, and **ANY** agreement `0 < t < n`
  inside half the `Θ(√n)` strip `(k - 1) - t²/n ≤ t(n - t) / (2 n ⌈√(n - 1)⌉)`:
  $$\Lambda\bigl(\mathrm{RS}(D, k)^{\bowtie w},\; \tfrac{n - t}{n}\bigr) \le
  \left\lfloor \frac{n \cdot (\lceil\sqrt{n - 1}\rceil + 1)^3}{n - t} \right\rfloor
  = O\!\left(\frac{n^{3/2}}{1 - t/n}\right).$$

### 1.2 Universal All-Length Bounds (`n ≥ 256`, All Fields, Injective Domains, Arbitrary Widths)

Specializing `cubic_hahn_of_ratio_cap` with `r₀ = t²/n - c · t(n - t)/n` gives single-step
and two-step bounds for all four challenge rates and all lengths `n ≥ 256`:

| Rate | Step | `MultipleOmissionJohnson` | **New `UniformCubicHahnBracket`** | Gain |
| :--- | :---: | :---: | :---: | :---: |
| `1/2` | `J+1` | `40n` | **`11n`** (`c = 3/23`) | `3.64×` |
| `1/4` | `J+1` | `32n` | **`7n`** (`c = 1/5`) | `4.57×` |
| `1/8` | `J+1` | `14n` | **`6n`** (`c = 1/4`) | `2.33×` |
| `1/16` | `J+1` | `14n` | **`5n`** (`c = 3/11`) | `2.80×` |
| `1/2` | `J+2` | `1584n` | **`61n`** (`c = 1/14`) | `26.0×` |
| `1/4` | `J+2` | `512n` | **`14n`** (`c = 3/26`) | `36.6×` |
| `1/8` | `J+2` | `58n` | **`10n`** (`c = 1/7`) | `5.8×` |
| `1/16` | `J+2` | `19n` | **`9n`** (`c = 4/25`) | `2.1×` |

Lean theorems: `four_rate_safe_plus_one` and `four_rate_safe_plus_two`.

### 1.3 Official `SmoothListRankBracket` (`RankReview.listAnswer`) Upgrades

1. **`first_failure_plus_one_tight`**: preserves `n - agreements n k + 1 ≤ e.val` under
   `2.3×–4.6×` smaller smooth fields (`![11, 7, 6, 5] * n ≤ |F| / 2¹²⁸`).
2. **`first_failure_plus_two`** & **`first_failure_plus_two_reserved`**: **strictly advance**
   the universal lower endpoint of `RankReview.listAnswer` across all four rates and all
   smooth lengths `n ≥ failureLength j` to **`n - agreements n k + 2 ≤ e.val`**.
3. **`production_super_johnson_listAnswer`**: on ANY length-`2³⁰` smooth domain over a
   `< 2²⁵⁶` field with `superJohnsonBudget j ≤ |F| / 2¹²⁸` (including 190-to-255-bit smooth
   fields such as BLS12-381), pushes `RankReview.listAnswer` strictly past Johnson by
   **`+4,799` (`314,496,499`), `+8,192` (`536,879,106`), `+10,592` (`694,127,355`), and
   `+12,288` (`805,318,659`)** full integer errors!

---

## 2. Hahn–Hint Boosted Boundary-Shell Exclusions (`B₂ = 2³¹`)

**Lean module:** `ArkLib/Research/ProximityGap/Frontier/CubicHintBoundaryShell.lean`

A single hint codeword with agreement set $H_{\text{set}}$ of size $H$ intersecting every
other codeword's agreement set $S_i$ (`|S_i| = t`) in at most $d$ coordinates strictly boosts
the degree-1 Hahn sum from $0$ to the exact variance floor (`sum_P1_hint_lower`):

$$\sum_{i,j=1}^{m} P_1(n, t, |S_i \cap S_j|) \ge m^2 \cdot \frac{(Ht - nd)^2}{n H (n - H)}
\qquad (nd \le Ht).$$

Plugging this positive floor into `quadratic_hahn_block_bound_with_hint` and
`cubic_hahn_block_bound_with_hint` strictly tightens ALL FOUR `B₂ = 2³¹` production
over-budget boundary shells relative to degree-1 `HintBoundaryShell`:

| Rate & Step (`B₂ = 2³¹`) | Degree-1 `HintBoundaryShell` | **New `CubicHintBoundaryShell`** | Improvement | Mode / `r₀` |
| :--- | :---: | :---: | :---: | :---: |
| `1/2`, `J+1` (`e = 314,491,700`) | `< 759,265,175` (`A_J + 15,050`) | **`< 759,263,558` (`A_J + 13,433`)** | `1.12×` | Cubic (`r₀ = 314,091,338`) |
| `1/4`, `J+1` (`e = 536,870,914`) | `< 536,905,668` (`A_J + 34,757`) | **`< 536,903,681` (`A_J + 32,770`)** | `1.06×` | Cubic (`r₀ = -53,742`) |
| `1/8`, `J+2` (`e = 694,116,764`) | `< 379,666,627` (`A_J + 41,565`) | **`< 379,661,358` (`A_J + 36,296`)** | `1.15×` | Quadratic (`P₁` boost) |
| `1/16`, `J+1` (`e = 805,306,371`) | `< 268,479,191` (`A_J + 43,737`) | **`< 268,467,184` (`A_J + 31,730`)** | **`1.38×`** | Quadratic (`P₁` boost) |

---

## 3. Quadratic Hahn Forced Saturated-Pair Density and `K₄` Cliques (`B₂ = 2³¹`)

**Lean module:** `ArkLib/Research/ProximityGap/Frontier/QuadraticHahnCliques.lean`

Applying `sum_P1_nonneg` and `sum_P2_nonneg` to the concave penalty $(d - s)(s - r_0)$
with $r_0 = \max(0, 2t - n) - 1$ (`forced_edges_quadratic_hahn`, `forced_clique_quadratic_hahn`)
charges every non-saturated pair $s_{\min} \le s \le d - 1$ at least
$\min((d - s_{\min})(s_{\min} - r_0),\; d - 1 - r_0) > 0$, while saturated pairs ($s = d$)
pay $0$.

Across the `B₂ = 2³¹` (`M = 2³¹ + 1`) open list fronts, this crosses the Turán $K_4$ threshold
($2/3 = 66.67\%$) where degree-1 incidence fell far below even the triangle threshold ($50\%$):

| Front (`n = 2³⁰`, `B₂ = 2³¹`) | Degree-1 Density | **Quadratic Hahn Density** | Forced Structure | Lean Theorems |
| :--- | :---: | :---: | :---: | :--- |
| Rate `1/2`, `J+1` (`e = 314,491,700`) | `49.07%` (no `K₃`) | **`≥ 74.07%`** (`s_min = 2t - n`) | **Saturated `K₄`** | `rate_half_second_budget_K4`, `rate_half_second_budget_rs_K4` |
| Rate `1/16`, `J+1` (`e = 805,306,371`) | `40.63%` (no `K₃`) | **`≥ 68.75%`** (`s_min = 0`) | **Saturated `K₄`** | `rate_sixteenth_second_budget_K4`, `rate_sixteenth_second_budget_rs_K4` |
| Rate `1/8`, `J+2` (`e = 694,116,764`) | `12.01%` | **`≥ 32.90%`** (`2.74×` gain) | Dense saturated pairs | `rate_eighth_j2_second_budget_edges` |

In particular, on both Rate `1/2` `J+1` and Rate `1/16` `J+1` at the second prime budget
`B₂ = 2³¹`, any over-budget scalar Reed–Solomon list unconditionally forces **4 distinct
message polynomials whose 6 pairwise differences all split completely into `k - 1` distinct
roots inside the evaluation domain**.
