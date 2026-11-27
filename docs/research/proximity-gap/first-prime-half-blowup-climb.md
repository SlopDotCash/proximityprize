# First-Prime Half-Rate Blown-Up Gauss-Graph Climb Through `312,400,000` Errors

## Status and Honesty Scope

- **Open bracket (first designated prime, rate $1/2$):**
  On `PrizeShapePrimeP30` ($P_1 = 2^{30}(2^{128}+192)+1$, $n = 2^{30} = 1{,}073{,}741{,}824$, $k = 2^{29}$, $d = 2^{29}-1$, $B_1 = \lfloor P_1 / 2^{128} \rfloor = 2^{30}$), the proven MCA first-failure bracket is `[268,435,457, 313,174,699]`.
- **What is 100% kernel-checked in `ArkLib/Research/ProximityGap/Frontier/FirstPrimeHalfBlowupClimb.lean`:**
  1. Existence and rank surpluses of both mixed-Hasse interpolation surfaces (`(54, 76, 44746)` and `(102, 144, 5412)`) at `e = 312,400,000` errors (`t = 761,341,824`, `miss = 7,000`, `core = 761,334,824`) on every injective domain of length $2^{30}$ over any field (`ranks`, `surfaces`).
  2. Strict parameter, forced collinearity (`n + 2d < 3 \cdot \mathrm{core}`), Veronese-gap, tame characteristic (`< 2^{100} < P_1`), and dual-constraint `(α, β)` pricing certificates (`parameters`, `dual_prices_le_three`, `dual_prices_four_plus`).
  3. **Non-exceptional (`j ≤ 3`) safety (`non_exceptional_safe`):** Every admissible allocation with $j \in \{0, 1, 2, 3\}$ rich polynomial affine heads (together with all nonlinear irreducible factors, nonaffine linear factors, small heads, scalar-only factors, and the primary/companion resultant) has total bad-scalar count at most **`1,067,196,929 < B_1 = 1,073,741,824`** (slack `6,544,895`).
  4. **Forced collinear `4 ≤ j ≤ 76` reduction (`collinear_four_head_reduction`):** Across all remaining $4 \le j \le 76$ rich-head counts allowed by the primary surface (`76`, tightening `RateHalfRichHeadCensus`'s `118`), the entire non-head bad-scalar contribution is at most **`126,933,994`**. Any over-budget received pair must therefore have its collinear rich heads alone carry at least **`946,807,831`** bad scalars.
  5. **Four-core overlap and direction-degree cap (`four_core_overlap_and_direction_cap`):** Any four cores of size $\ge 761{,}334{,}824$ on a length-$2^{30}$ domain contain a distinct pair intersecting on at least **`478,242,187`** sites, forcing the coprime common direction degree to satisfy **`m ≤ 58,628,724`**.
- **What remains written geometry / open:**
  - The blown-up surface intersection and projective plane-curve duality bridge from MCA bad scalars to the allocation hypotheses is written in [`half-blowup-gauss-window.md`](half-blowup-gauss-window.md) (building on [`HalfBlowupGaussWindow.lean`](../../../ArkLib/Research/ProximityGap/Frontier/HalfBlowupGaussWindow.lean)).
  - **Open residual family:** The `4 ≤ j ≤ 76` collinear rich-head family (precisely the family realizing failure at `313,174,699` in `FirstPrimeSepticCores.lean`) remains **open** in `[268,435,457, 312,400,000]`. This result eliminates every non-exceptional (`j ≤ 3`) and non-collinear obstruction across **`98.27%`** of the open bracket (`+43,964,543` errors above `268,435,457`), isolating `4 ≤ j ≤ 76` collinear heads as the sole remaining mechanism.

---

## Surface Parameters and Per-`j` Breakdown at `e = 312,400,000`

| Quantity | Value |
|---|---:|
| Length $n$ / degree $d$ / budget $B_1$ | `1,073,741,824` / `536,870,911` / `1,073,741,824` |
| Error count $e$ / agreement $t = n - e$ | `312,400,000` / `761,341,824` |
| Miss threshold / core size | `7,000` / `761,334,824` |
| Primary surface $P_1 = (r_1, v_1, s_1)$ | `(54, 76, 44746)`, surplus `202,506,832` |
| Companion surface $Q_2 = (r_2, v_2, s_2)$ | `(102, 144, 5412)`, surplus `7,072,525,648` |
| Resultant $v_1 s_2 + v_2 s_1$ / linear cap | `6,854,736` / `21` |
| Veronese tiers at $j = 0$ | `(6, 5)`, `(12, 10)`, `(24, 20)` |
| Dual prices at $j = 0$ | $\alpha_0 = 52{,}991$, $\beta_0 = 14{,}109$ |

| Rich heads $j$ | Rich-head mass | Max non-head mass | Total cap | Status vs $B_1 = 2^{30}$ |
|---:|---:|---:|---:|---|
| `0` | `0` | `298,273,406` | `298,273,406` | **SAFE** (`-775,468,418`) |
| `1` | `312,400,001` | `259,664,655` | `572,064,656` | **SAFE** (`-501,677,168`) |
| `2` | `624,800,002` | `133,098,836` | `757,898,838` | **SAFE** (`-315,842,986`) |
| `3` | `937,200,003` | `129,996,926` | **`1,067,196,929`** | **SAFE** (`-6,544,895`) |
| `4 ≤ j ≤ 76` | collinear ($\ge 946{,}807{,}831$ needed) | **`≤ 126,933,994`** | — | **OPEN** (collinear only, $m \le 58{,}628{,}724$) |

---

## Verification and Reproduction

- **Lean kernel verification:**
  ```bash
  scripts/pg-iterate.sh ArkLib/Research/ProximityGap/Frontier/FirstPrimeHalfBlowupClimb.lean
  ```
- **Independent exact-integer probe:**
  ```bash
  python3 scripts/probes/probe_first_prime_half_blowup_climb.py
  ```
