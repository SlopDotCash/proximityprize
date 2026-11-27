# Blown-Up Gauss-Graph Excess Intersection and Dual `(α, β)` Veronese Windows at Eighth Rate

This note applies the nef-safe blown-up Gauss-graph height bound (`blowupH`, introduced in
`half-blowup-gauss-window.md`), dual-constraint `(α, β)` Veronese pricing, and an unconditionally
Lean-proved Lagrange Veronese row-independence theorem (`p = min(j, s + 1)`) to four eighth-rate
(`n = 2^{30}`, `k = 2^{27}`, `d = 2^{27} - 1`, `B_2 = 2^{31}`) second-prime production windows.

## Summary of Production Windows

| Window | Errors $e$ | Primary $(r_1, b_1, s_1)$ | Companion $(r_2, b_2, s_2)$ | $L$ | `linMult` | $j = 4$ Residual | Non-Exceptional Max | Slack below $2^{31}$ |
|---|---:|---|---|---:|---:|---:|---:|---:|
| **W0** (Safe predecessor) | `671,088,639` | `(6, 16, 335)` | `(10, 29, 126)` | `335` | `17` | **`189,082`** | **`2,125,303,109`** | **`+22,180,539`** |
| **W1** ($5k$ successor) | `671,088,640` | `(6, 16, 335)` | `(10, 29, 126)` | `335` | `17` | **`189,082`** | **`2,125,303,112`** | **`+22,180,536`** |
| **W2** ($(1,1,1,6)$ climb) | `677,920,000` | `(8, 23, 680)` | `(14, 41, 244)` | `680` | `18` | **`711,893`** | **`2,147,458,563`** | **`+25,085`** |
| **W3** (Ceiling-1) | `679,477,247` | `(9, 25, 887)` | `(16, 46, 296)` | `1300` | `18` | **`1,090,505`** | **`2,136,590,428`** | **`+10,893,220`** |

Key advances over `tangent-polar-windows.md` and `eighth-successor-tight-window.md`:

1. **109.0× reduction of the `671,088,640` residual**: from `20,607,410` (published `main`) and
   `397,364` (Sparse-Gauss) down to **`189,082`**.
2. **Unconditional predecessor slack boost at `671,088,639`**: max bad labels drops from
   `2,128,274,755` (slack `19,208,893`) to **`2,125,303,109`** (slack **`+22,180,539`**,
   shaving `99.1%` of the non-four-head residual overhead).
3. **New `(1,1,1,6)` safety climb record**: climbs `+320,000` higher than Sparse-Gauss (`677,600,000`)
   to **`677,920,000`** (`+6,831,360` past `5k`, covering **`81.4%`** of the open bracket
   `[671,088,640, 679,477,248]`).
4. **Ceiling-1 tightening (`679,477,247`)**: cuts the `j = 4` residual **2.22×** from `2,416,639`
   down to **`1,090,505`**, leaving `+10,893,220` slack on all non-exceptional allocations
   (`j ≤ 3`, collinear `j ≥ 4`, `(1,1,1,7+)`, and `j ≥ 6` collinear).
5. **Sharpened `671,088,640` structural floors**:
   - Saturated `(1,1,1,1)` distinct double-site orbit floor: **`B ≥ 268,340,910`**
     (within **`94,544`** of the 2-to-1 double-site threshold `2d = 268,435,454`, i.e., `> 49.982%`
     of all `4d = 536,870,908` double sites).
   - Profile `(1,1,1,5)` fresh-label collision cap: **`≤ 189,085`** across all four heads
     (`> 99.991%` of all `2,147,483,652` fresh slots collision-free).
   - Arbitrary non-Galois homothetic-cover image floor across all `0 ≤ s ≤ 4`:
     **`|h(H_reg)| ≥ 670,994,076`** (`> 0.6249 n`), isolated singleton fibers **`≥ 268,246,328`**,
     and partial-involution pair cap **`P ≤ 402,747,748`**.

## Verification Scope

- **Lean-checked (`ArkLib/Research/ProximityGap/Frontier/EighthBlowupDualWindow.lean`)**:
  zero `sorry`, zero custom axioms (`#print axioms` $\subseteq$ `{propext, Classical.choice, Quot.sound}`):
  - `factor_order_sum_ge` and `blowupH_mono` (nef-safe blown-up Gauss-graph algebraic core).
  - `veronese_lagrange_separation` and `veronese_eval_linearIndependent`: over any field `F`
    (arbitrary characteristic, no general-position assumption), any `p ≤ s + 1` pairwise distinct
    points in `F²` have linearly independent evaluation functionals on degree-`≤ s` bivariate
    polynomials, formally certifying `p = min(j, s + 1)` fixed rich-head rows.
  - `ranks` and `surfaces`: exact positive mixed-Hasse surpluses and surface existence for all
    eight production surfaces across W0–W3 on any injective length-`2^{30}` domain.
  - `parameters`, `dual_prices`, and `allocation`: exact verification of all denominators,
    5-column conic and 7-tier Veronese gaps, tame-characteristic guards, Case-1 fallback floors,
    nonaffine linear folding (`linMult ≤ alpha`), and dual-constraint `(α, β)` allocations.
  - `blowup_sharpened_floors`: exact arithmetic consequences for `(1,1,1,1)` orbits, `(1,1,1,5)`
    collisions, and universal homothetic covers.
- **Written mathematical steps**:
  - The nef-safe blown-up Gauss-graph intersection bound on
    $\operatorname{Bl}_{\bigcup C_x}\operatorname{Bl}_\Sigma \mathbf{P}_{\mathbf{P}^1_X}(\mathcal{O} \oplus \mathcal{O} \oplus \mathcal{O}(-d))$
    and Case 1 / Case 2 factor split follow `half-blowup-gauss-window.md` (Section 1).
  - Plane-curve reflexivity, subtraction at infinity (`2sb`), and the 5-column conic / Veronese
    determinant extractions follow `tangent-polar-windows.md` and `half-sparse-gauss-window.md`.
  - Notice at W2 and W3 (`e > 671,088,640`), `15c > 3n + 20d` and `13c > 3n + 13d` force all
    `j ≥ 6` rich heads collinear and every `j = 5` family to contain 4 collinear heads, while
    noncollinear `4 + 1` and `3 + 1` (plus `(1,1,1,q)` with `q ≤ 5` at W2 and `q ≤ 6` at W3)
    remain the open head configurations above `5k`.
- **Independent Python probe (`scripts/probes/probe_eighth_blowup_dual_window.py`)**:
  reproduces all eight rank surpluses, all `(j, b, m)` Veronese/conic prices, all `(α, β)` dual
  bounds, and all sharpened floors.

## Veronese Ladder and Conic Determinant

Because `3t < n + 2d` at eighth rate, the triangle determinant is replaced by the 5-column
conic-modulo-equation determinant at `m = b = 2` (`gap = 5t - n - 6d > 0`, `h = 5`, `a = 1`,
`E = 6`, Bezout `≤ 4 = 2m`) together with the 7-tier Veronese determinant ladder using
`p = min(j, s + 1)` unconditionally independent fixed rich heads:

| Tier $(s, a)$ | $h = \binom{s+2}{2}$ | $C_a = \binom{a+2}{3}$ | $E_s = \frac{s(s+1)(s+2)}{3}$ | Reflexivity guard | Max fixed heads $p$ |
|---|---:|---:|---:|---|---:|
| Conic (5-col) | `5` | `1` | `6` | `m = b = 2` | `0` |
| `(2, 1)` | `6` | `1` | `8` | `m > 2` | `min(j, 3)` |
| `(3, 2)` | `10` | `4` | `20` | `m > 6` | `min(j, 4)` |
| `(4, 2)` | `15` | `4` | `40` | `m > 12` | `min(j, 5)` |
| `(5, 3)` | `21` | `10` | `70` | `m > 20` | `min(j, 6)` |
| `(6, 4)` | `28` | `20` | `112` | `m > 30` | `min(j, 7)` |
| `(8, 5)` | `45` | `35` | `240` | `m > 56` | `min(j, 9)` |
| `(10, 6)` | `66` | `56` | `440` | `m > 90` | `min(j, 11)` |

For every window `w` and head count `0 ≤ j ≤ b₁`, the dual-constraint verification checks that
every irreducible nonlinear factor `(b, m)` satisfies `m * factorUnitPrice(w, j, b, m) ≤ m * α(w, j) + b * β(w, j)`
and every nonaffine common linear factor satisfies `linMult ≤ α(w, j)`, yielding
`total ≤ ordHeadMass(w, j) + fixedOverhead(w, j) + (s₂ - j) α(w, j) + (b₁ - j) β(w, j) ≤ ordBound < 2^{31}`.
