# Universal Multi-Head Barriers & 4-Head Collinear Cross-Ratio Obstructions on `[447,392,428, 480,946,858]`

## Summary

This note accompanies [`QuarterFourHeadCrossRatioBarrier.lean`](../../../ArkLib/Research/ProximityGap/Frontier/QuarterFourHeadCrossRatioBarrier.lean) and [`probe_quarter_four_head_cross_ratio.py`](../../../scripts/probes/probe_quarter_four_head_cross_ratio.py).

We formalize two interlocking sets of obstructions governing first-prime quarter-rate MCA ($n = 2^{30}$, $k = 2^{28}$, $d = 2^{28} - 1$, $D = 268{,}435{,}454$) across `[447,392,428, 480,946,858]`:

1. **Universal Quotient-Free Discrete Johnson Hull, `H ≥ 5` Barrier, Multi-Fresh `b ≥ 2` Exclusion, & Rational-Curve Degree Floor (`discrete_johnson_hull`, `p1_quarter_five_plus_heads_impossible`, `p1_quarter_multifresh_above_johnson_impossible`, `nonlinear_curve_pencil_degree_floor`, `p1_quarter_four_head_threshold`, `universal_label_core_conservation_barriers`):**
   - For **every** integer $H \ge 5$ (both 2D planar and 1D collinear, **zero** quotient, rank, or symmetry assumptions), instantiating the discrete Johnson hull $2 a \sum |C_i| \le H(H-1) d + a(a+1) n$ at $a = \lfloor H / 2 \rfloor$ forces every 1-fresh witness on $p_1$ quarter-rate to have **$e \ge 483{,}183{,}821 > 480{,}946{,}859$** ($H = 5: 483.18\text{M}$, $H = 6: 492.13\text{M}$, monotonically increasing toward Johnson $536.87\text{M}$).
   - **Uniform multi-fresh exclusion (`p1_quarter_multifresh_above_johnson_impossible`):** Every uniform $b$-fresh linear-head witness strictly above the Johnson radius ($2 \le b \le 55{,}924{,}050$) is forced to $H \ge 2b + 1$ and $e \ge 480{,}946{,}859$ — confining every uniform linear-head beat above Johnson to **`b = 1` AND `H ∈ {2, 3, 4}`**.
   - **Rational-curve degree floor (`nonlinear_curve_pencil_degree_floor`):** Any non-linear rational curve family beating the budget requires curve degree $\ge 432{,}479{,}348$ on $p_1$ quarter-rate (and $\ge 626{,}349{,}400$, $447{,}392{,}430$, $671{,}088{,}643$, $594{,}392{,}800$ on the other four open ceilings), eliminating all $o(n)$ conic/hyperelliptic curve pencils.
   - For $H = 4$, instantiating at $a = 2$ proves the exact threshold **$e \ge 469{,}762{,}048$** ($7n/16$).
   - Companion label-core conservation bounds certify the universal $p_2$ head-count floors ($H \le 4 \Rightarrow e \ge 536{,}870{,}912$, $H = 5 \Rightarrow e \ge 429{,}496{,}729$, $H = 6 \Rightarrow e \ge 357{,}913{,}941$).
2. **Exact 5-Partition Site Inequality for 4 Collinear Heads (`four_head_five_partition_pointwise`, `four_head_five_partition_global`):**
   - Classifying every site $x \in I$ by the equivalence partition of $(f_0(x), f_1(x), f_2(x), f_3(x))$ into $(1,1,1,1)$, $(2,1,1)$, $(2,2)$, $(3,1)$, $(4)$ proves directly on `Finset I`:
     $$2 \sum_{i=0}^3 |\mathrm{core}_i| + \sum_{x \in I} \mathrm{fresh}(x) + n_{22} + 2 n_4 \le 4 |I| + \sum_{0 \le i < j \le 3} |E_{ij}|,$$
     strictly sharpening `QuarterCollinearInterval.lean`'s `four_head_slack` by the exact $(2,2)$ and $(4)$ defects $n_{22} + 2 n_4$.
3. **Algebraic Cross-Ratio Pencil & Exact Constant-Cross-Ratio 4-Fiber Factorization (`cross_ratio_pencil_identity`, `cross_ratio_triple_common_root`, `cross_ratio_quadruple_double_root`, `cross_ratio_double_pair_sq_root`, `constant_cross_ratio_four_fiber_factorization`):**
   - For any four collinear heads normalized to $(0, P, Q, R)$ of degree $\le D$ over any field $K$, the Plücker/cross-ratio identity
     $$P(Q - R) + R(P - Q) = Q(P - R)$$
     yields a pencil $(A, B, C)$ whose common divisor absorbs every $(3,1)$ triple coincidence to order $\ge 1$ and every $(4)$ quadruple coincidence to order $\ge 2$, while every $(2,2)$ site is a double root of one of $(A, B, C)$.
   - When the cross-ratio is constant ($A = c \cdot C$ with $c \in K \setminus \{0, 1\}$), Euclidean-domain factorization over $K[X]$ proves
     $$P = H U (c V - U), \qquad Q = H V (c V - U), \qquad R = H (c - 1) U V$$
     with $\gcd(U, V) = 1$ and $2 \max(\deg U, \deg V) + \deg H \le \max(\deg P, \deg Q, \deg R) \le D$ — forcing a **4-fiber rational map $U / V$** of degree $m_0 \le (D - \deg H)/2 \le 2^{27} - 1$.
4. **4-Head Cross-Ratio Dichotomy on `[469,762,049, 480,946,858]` & Pullback / Tower Exclusions (`four_head_cross_ratio_dichotomy`, `four_head_const_cr_degree_floor`, `four_head_cyclic_pullback_exclusions`, `four_fiber_depth3_tower_exclusion`):**
   - At every error count $e = 469{,}762{,}049 + j_4 \in [469{,}762{,}049,\; 480{,}946{,}858]$ ($0 \le j_4 \le 11{,}184{,}809$), every 4-head collinear overrun satisfies:
     - $n_{22} + 2 n_4 \le 3 + 8 j_4$,
     - $n_{31} + 2 n_4 \ge \lceil (536{,}870{,}897 - 8 j_4)/2 \rceil$ ($\ge 268{,}435{,}449$ at $j_4 = 0$; $\ge 223{,}696{,}213$ at $480{,}946{,}858$),
     - reduced cross-ratio degree $M_0 \le D + 5 + 4 j_4$ ($\le D + 5$ at $469{,}762{,}049$; $\le 313{,}174{,}695$ at $480{,}946{,}858$),
     - **exact cross-ratio missing-root cap:** $3 M_0 - (n_{211} + n_{22}) \le 3 + 8 j_4$.
   - At the first 4-head threshold $e = 469{,}762{,}049$ ($j_4 = 0$), **either** the cross-ratio is constant (forcing a 4-fiber map $U/V$ of degree $2^{27}-1$ missing at most **1** root across all 4 fibers) **or** the cross-ratio pencil $(A_0, B_0, C_0)$ has degree $1 \le M_0 \le D + 5$ missing at most **3** roots total across all 3 fibers (and if $223{,}696{,}216 \le M_0 \le D$, $(A_0, B_0, C_0)$ itself already triggers a 3-head overrun at or before $469{,}762{,}048$!).
   - **Cyclic pullback exclusions (ANY field, including $p_1$ and $p_2$):** ZERO general 4-head collinear pullbacks on $\mu_M$ ($M \le 64$) and ZERO primitive ($h = 0$) constant-cross-ratio 4-head pullbacks on $\mu_M$ ($M \le 128$) can beat `480,946,859`; on $\mu_{128}$, the **only** arithmetically surviving constant-cross-ratio tuple is $h = 1, m_0 = 15, n_{31} = 60$ (all four degree-15 fibers 100% full), and any general 4-head pullback on $\mu_{128}$ must satisfy $182 \le \Delta_4 \le 186$ (slack $\le 4$ across all 6 degree-31 differences).
   - **Infinite-tower characteristic-zero 4-fiber exclusion (`four_fiber_depth3_tower_exclusion`):** Combining with the Depth-$L$ Fourier Parity Theorem ([`QuarterMu64Mu128CyclicExclusion.lean`](../../../ArkLib/Research/ProximityGap/Frontier/QuarterMu64Mu128CyclicExclusion.lean)), ZERO full 4-split constant-cross-ratio pencils beating `480,946,859` exist on $\mu_{2^k}$ for every $k \ge 8$ ($N \ge 256$) in characteristic zero.

## Honesty Boundary

- **100% axiom-clean Lean (`QuarterFourHeadCrossRatioBarrier.lean`):** All 18 public theorems are proved with Mathlib-only imports, 0 `sorry`, 0 warnings, and `#print axioms` $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$.
- **Scope:** The universal $H \ge 5$ barrier applies to all 1-fresh witnesses (`|C_i| ≥ n - e - 1`); the 4-head collinear site inequality and cross-ratio factorization hold over arbitrary fields without symmetry assumptions; the infinite-tower 4-fiber exclusion (`four_fiber_depth3_tower_exclusion`) applies to characteristic zero (and any finite subgroup $\mu_N$ with complex ratio transfer, such as $\mu_{64}$ and $\mu_{128}$ via `mu64-unit-lattice-transfer.md` / `mu128-unit-ellipsoid-transfer.md`).
