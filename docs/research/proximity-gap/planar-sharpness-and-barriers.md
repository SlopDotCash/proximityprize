# Universal Planar Meeting-Excess Sharpness and Quotient-Free MCA Barriers

## Status and Honesty Scope

- **100% kernel-checked standalone Mathlib-only Lean module (`ArkLib/Research/ProximityGap/Frontier/PlanarSharpnessAndBarriers.lean`):**
  Every theorem in this module is completely unconditional, depends only on Mathlib (zero project-specific axioms, zero `sorry`, strictly standard Lean axioms `{propext, Classical.choice, Quot.sound}`), and applies over arbitrary fields and arbitrary finite evaluation domains.
- **Discovery attribution:**
  The barrier and sharpness formulations were mapped in Wave 4 (`@prize-mapper`, board `#177`) and proved here in full generality (extending the 4-cubic `≤ 12` meeting bound to arbitrary degree `d` via a characteristic-free two-case determinant / Bézout factorization proof!).

---

## Theorem 1 — Universal `4d` Meeting-Excess Bound for Four Non-Collinear Pairs

**Theorem (`four_noncollinear_meeting_excess_le`):** Over **any** field $F$ (any characteristic), let $(U_i, V_i) \in F[X]_{\le d}^2$ ($i \in \mathrm{Fin}\ 4$) be four pairwise-distinct polynomial pairs not all collinear over $F(X)$. For any finite set $S \subseteq F$, define the site meeting excess $e_x = 4 - |\{(U_i(x), V_i(x)) : i \in \mathrm{Fin}\ 4\}|$. Then
$$\sum_{x \in S} e_x \le 4 d.$$

**Proof architecture (characteristic-free, two cases):**
- **Case A (all four triples non-collinear):** All four oriented determinants $\Delta_{ijk} = (U_j - U_i)(V_k - V_i) - (U_k - U_i)(V_j - V_i)$ are nonzero of degree $\le 2d$. At any site $x$, any coincident pair forces $(X - x) \mid \Delta_{ijk}$ and any coincident triple forces $(X - x)^2 \mid \Delta_{ijk}$ directly from polynomial divisibility (no derivatives needed). Checking all partitions of $\mathrm{Fin}\ 4$ gives $2 e_x \le \sum_{\{i,j,k\}} \operatorname{mult}_x(\Delta_{ijk})$, whence $2 \sum_{x \in S} e_x \le 4(2d) = 8d$.
- **Case B (some triple collinear, w.l.o.g. `{0, 1, 2}`):** Because $(0,1,2)$ is collinear and the quartet is non-collinear, $\Delta_{013} \ne 0$. Factoring $A = \gcd(U_1 - U_0, V_1 - V_0)$ gives coprime direction polynomials $(S_{\mathrm{dir}}, T_{\mathrm{dir}})$ of max degree $m$ with Bézout identity $p S_{\mathrm{dir}} + q T_{\mathrm{dir}} = 1$. Setting $B = p(U_2 - U_0) + q(V_2 - V_0)$, $C = B - A$, and $\delta_3 = S_{\mathrm{dir}}(V_3 - V_0) - T_{\mathrm{dir}}(U_3 - U_0)$ yields four nonzero polynomials with $\deg A, \deg B, \deg C \le d - m$ and $\deg \delta_3 \le d + m$. Since $(S_{\mathrm{dir}}(x), T_{\mathrm{dir}}(x)) \ne (0,0)$, every meeting among `{0,1,2}` kills $A$, $B$, or $C$, and every meeting involving `3` kills $\delta_3$, giving $\sum_{x \in S} e_x \le 3(d - m) + (d + m) = 4d - 2m \le 4d$.

**Immediate corollaries:**
- `four_noncollinear_cubics_le_twelve` ($d = 3 \implies \sum e_x \le 12$): certifies that both `SecondPrimePlanarQuartet.lean` (`553,648,129` on `p2` quarter-rate) and `EighthTransverseAttack.lean` (`679,477,248` on `p2` eighth-rate) attain the **universal maximum** `12` among all 4-cubic planar arrangements.
- `four_noncollinear_septics_le_28` ($d = 7 \implies \sum e_x \le 28$): certifies the universal saturation ceiling for 4-septic planar quartets over any field and domain.

---

## Theorem 2 — Universal Quotient-Free Label-Core & `H`-Count Barriers

Using `label_core_conservation` ($H c + L \le H n$), `discrete_johnson_hull` ($2 a H c \le H(H-1)d + a(a+1)|\mathrm{Cov}|$), and `continuous_johnson_hull` ($(Hc)^2 \le |\mathrm{Cov}|(Hc + H(H-1)d)$) with **zero quotient or rank assumptions**:

| Target | Constraint | Universal Lower Bound on First-Failure `e` | Lean Theorem |
|---|---|---:|---|
| `p2` half-rate (`B = 2^31`) | `H ≤ 4` / `H = 5` / `H = 6` | `≥ 536,870,912` / `≥ 429,496,729` / `≥ 357,913,941` | `p2_head_count_barriers` |
| `p2` quarter-rate (`B = 2^31`) | `H ≤ 4` | `≥ 536,870,912` (`1/2 n`) | `p2_head_count_barriers` |
| `p1` quarter-rate (`B = 2^30`) | **All `H ≥ 5`** (2D planar & 1D collinear) | **`≥ 483,183,821 > 480,946,859`** | `p1_quarter_five_plus_barrier` |
| `p2` eighth-rate (`B = 2^31`) | **All `H ≥ 2` 1D collinear** | **`≥ 683,871,281 > 679,477,248`** | `p2_eighth_collinear_barrier` |

---

## Theorem 3 — Exact Global Full-Rank 2D Optimality of `SecondPrimeCyclicCubics`

**Theorems (`full_rank_planar_core_cap`, `second_prime_half_full_rank_optimal`):**
For any full-rank 2D planar quotient arrangement ($M = 2K \ge 8$, $H \ge 4$, $r + D \le K$, $E \le (H-1)(D+1) - 2$) exceeding `p2`'s label budget ($H(2K - c) > 4K$), the core fraction satisfies
$$\frac{c}{2K} \le \frac{31}{48},$$
with equality **uniquely** at $K = 4, H = 6$ ($M = 8, D = 3, H = 6$, realized by `SecondPrimeCyclicCubics.lean` at `380,283,564` errors). Any further drop below `380,283,564` via single-quotient 1-fresh heads strictly requires an algebraic rank drop ($\operatorname{rank}(A_{\mathcal{C}}) < E$) or multi-fresh / non-quotient structure.

---

## Verification and Reproduction

- **Lean kernel verification:**
  ```bash
  scripts/pg-iterate.sh ArkLib/Research/ProximityGap/Frontier/PlanarSharpnessAndBarriers.lean
  ```
- **Independent Python verification:**
  ```bash
  python3 scripts/probes/probe_planar_sharpness_and_barriers.py
  ```
