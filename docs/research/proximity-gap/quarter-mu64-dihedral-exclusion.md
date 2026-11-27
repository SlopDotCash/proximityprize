# Complete Exclusion of Degree-$2^{25}$ Dihedral Pullbacks on $\mu_{64}$

## Summary

Together with `QuarterIntervalWronskianPullbacks.lean` (which forces every non-dihedral inner factor $T$ of any three-head attack beating `480,946,859` to satisfy $\deg T \ge 12,463,075$) and `mu32-quarter-list-threshold.md` (which eliminates all $\mu_{32}$ pullbacks $x^{2^{25}}$), the sole remaining small-quotient pullback family of degree $\le 2^{25}$ on $\mu_{2^{30}}$ was the **degree-$2^{25}$ dihedral reflection pullback** on $\mu_{64}$:
$$R(x) = V\!\left(x^{2^{24}} + \frac{c}{x^{2^{24}}}\right), \qquad c \in \mu_{64}.$$

Previously, [`quarter-root-score-symmetry.md`](quarter-root-score-symmetry.md) checked only endpoint sets forming at most two angular intervals (`32,504` even and `31,040` odd endpoint sets, $< 0.01\%$ of all disjoint $(7, 7)$ pairs) and only over $p_1$.

We now **completely eliminate 100% of all degree-$2^{25}$ dihedral reflection pullbacks on $\mu_{64}$** — both the odd fixed-point-free reflection ($c = \zeta_{64}$, 32 nodes, $\binom{32}{7}\binom{25}{7} \approx 1.62 \times 10^{12}$ endpoint pairs) and the even fixed-point reflection ($c = 1$, 33 nodes, $\binom{33}{7}\binom{26}{7} \approx 2.81 \times 10^{12}$ endpoint pairs) — over **both** designated primes $p_1 = 2^{30}(2^{128}+192)+1$ and $p_2 = 2^{30}(2^{129}+13)+1$ (indeed, over every prime $p > 2^{156}$ with $128 \mid p - 1$; and for odd reflections, every prime $p > 2^{136}$ with $128 \mid p - 1$).

## Proof Architecture

The proof splits into four exact stages:

### Stage 1: Score & Deficiency Reduction (Axiom-Clean Lean)

Formalized in `ArkLib/Research/ProximityGap/Frontier/QuarterMu64DihedralExclusion.lean`:
- `dihedral_deg_le_seven`: Any pullback $R(x) = V(x^{2^{24}} + c/x^{2^{24}})$ of degree $2d \cdot 2^{24} \le D = 268,435,454$ has outer degree $d \le 7$.
- `dihedral_score_le_36_of_deg_le_6`: Every $d \le 6$ achieves $\mu_{64}$-root score $2(r_A + r_B + r_C) - 6d \le 36$, so it cannot beat `480,946,859` ($S > 36 \cdot 2^{24} = 603,979,776$).
- `dihedral_deg7_root_floor`: At $d = 7$ ($m_0 = 14$), beating `480,946,859` forces total distinct $\mu_{64}$-root count $r_A + r_B + r_C \ge 40$ (total deficiency $\le 2$ out of $42$, covering roots outside the trace image, repeated roots, degree-$6$ heads, and fixed points $\{0, 32\}$).
- `dihedral_odd_reflection_forces_776`: For the odd reflection $c = \zeta_{64}$ (32 weight-2 nodes), permuting the three heads always yields $|A| = |B| = 7$ distinct trace roots and $|C| \ge 6$ distinct trace roots.
- `dihedral_even_reflection_forces_776_interior`: For the even reflection $c = 1$ (31 weight-2 interior nodes $\{1, \dots, 31\}$ and 2 weight-1 fixed points $\{0, 32\}$), disjointness of $A, B, C$ on $\{0, 32\}$ forces (up to permuting the three heads) $|A| = |B| = 7$ distinct roots in $\{0, \dots, 32\}$ and $|C| \ge 6$ distinct roots lying **entirely in the interior $\{1, \dots, 31\}$**.

### Stage 2: Trace Factorization & Descent to $\mathbb{Q}(\zeta_{64})^+$ (Axiom-Clean Lean)

Set $\omega = \zeta_{128}$ ($\omega^2 = \zeta_{64}$). The trace nodes are
$$s_j = 2\cos\!\left(\frac{(2j-1)\pi}{64}\right) = \omega^{2j-1} + \omega^{-(2j-1)} \quad (1 \le j \le 32, \text{ odd})$$
$$t_j = 2\cos\!\left(\frac{2\pi j}{64}\right) = \zeta_{64}^j + \zeta_{64}^{-j} \quad (0 \le j \le 32, \text{ even}).$$

- `trace_diff_factorization`: $(\alpha + \alpha^{-1}) - (\beta + \beta^{-1}) = \alpha^{-1}(\alpha\beta^{-1} - 1)(\alpha\beta - 1)$, so every trace difference is a $\{2\}$-unit in $\mathbb{Z}[\zeta_{128}]$, specifically
  $$|s_x - s_a| = |1 - \zeta_{64}^{x-a}| \cdot |1 - \zeta_{64}^{x+a-1}|, \qquad |t_x - t_a| = |1 - \zeta_{64}^{x-a}| \cdot |1 - \zeta_{64}^{x+a}|.$$
- `cross_ratio_neg_invariant`: For any two distinct $x, y \in C$, the cross-ratio
  $$\rho = \prod_{a \in A} \frac{s_y - s_a}{s_x - s_a} \prod_{b \in B} \frac{s_x - s_b}{s_y - s_b}$$
  is invariant under $\tau \in \operatorname{Gal}(\mathbb{Q}(\zeta_{128})^+ / \mathbb{Q}(\zeta_{64})^+)$ ($\omega \mapsto -\omega$, which negates every $s_j \mapsto -s_j$). Thus **$\rho$ always lies in the degree-16 totally real subfield $K = \mathbb{Q}(\zeta_{64})^+$** (for both odd and even reflections).
- Since every trace difference is a $\{2\}$-unit, $\rho$ is a $\{2\}$-unit in $K$. Swapping $A \leftrightarrow B$ if needed ensures $v_{\pi}(\rho) \ge 0$ at the unique prime $\pi \mid 2$ of $\mathcal{O}_K$, so $1 - \rho \in \mathcal{O}_K$.

### Stage 3: Exact Integer Norm Lift to Characteristic Zero

Since $128 \mid (p_1 - 1)$ and $128 \mid (p_2 - 1)$ (`mu64_dihedral_prime_headroom`), $\mathbb{Z}[\zeta_{128}]$ maps onto $\mathbb{F}_p$ with kernel $\mathfrak{P} \mid p$. Any finite-field ratio collision on $x, y \in C$ puts $1 - \rho \in \mathfrak{p} = \mathfrak{P} \cap \mathcal{O}_K$, so $p \mid N_{K/\mathbb{Q}}(1 - \rho) \in \mathbb{Z}$.

Using the exact triangle-expansion bound across the 16 real embeddings $\sigma_{2e+1}$ ($e = 0, \dots, 15$) of $K = \mathbb{Q}(\zeta_{64})^+$:
$$|N_{K/\mathbb{Q}}(1 - \rho)| = \prod_{e=0}^{15} |1 - \sigma_{2e+1}(\rho)| \le \sum_{M \subseteq \{0,\dots,15\}} \prod_{e \in M} |\sigma_{2e+1}(\rho)|,$$
the pure-integer interval certifier [`scripts/probes/probe_quarter_mu64_dihedral_norm.py`](../../../scripts/probes/probe_quarter_mu64_dihedral_norm.py) (zero floating point; exact outward-rounded integer enclosures at $2^{80}$ cosine precision and $1/1024$-bit log precision) certifies across all Galois-representative pairs:

| Reflection family | Pairs certified (up to Galois) | Worst pair | Exact integer upper bound | Margin below $p_1$ ($> 2^{158}$) |
| :--- | :---: | :---: | :---: | :---: |
| Odd ($c = \zeta_{64}$, 32 nodes) | All $31$ ($x=1, y \in \{2,\dots,32\}$) | $(1, 32)$ | $< 2^{136}$ | $> 22$ bits |
| Even ($c = 1$, 33 nodes, $x, y \in \{1..31\}$) | All $109$ ($x \in \{1,2,4,8\}, y > x$) | $(1, 31)$ | $< 2^{156}$ | $> 2$ bits |

By `norm_lift_eq_zero` and `mu64_dihedral_prime_headroom` ($2^{136} < 2^{156} < p_1 < p_2$), we get $N_{K/\mathbb{Q}}(1 - \rho) = 0$, hence $\rho = 1$ **in characteristic zero** for every pair $x, y \in C$!

### Stage 4: Exhaustive 16-Generator Cyclotomic-Unit Rank Sieve

By `dyadic_cyclotomic_prod`, every $|1 - \zeta_{64}^d|$ ($1 \le d \le 63$) factors completely over the **16 odd-index generators** $|1 - \zeta_{64}^{2k+1}|$ ($k = 0, \dots, 15$), whose logarithms are $\mathbb{Q}$-linearly independent (verified regulator determinant $|\det| \approx 2.234 \times 10^6 \ne 0$). By `unit_log_independence_to_kernel`, any characteristic-zero ratio constancy across a 6-subset $C$ forces the ternary indicator vector $w = \mathbf{1}_A - \mathbf{1}_B \in \{-1, 0, 1\}^{\text{sites}}$ into the kernel over $\mathbb{Z}$ — hence over $\mathbb{Z}/m\mathbb{Z}$ for every $m$ — of the $81 \times n_{\text{sites}}$ matrix formed by the $5 \times 16 = 80$ exponent-difference equations plus $\sum_z w_z = 0$.

The exhaustive verifier [`scripts/probes/probe_quarter_mu64_dihedral_sieve.py`](../../../scripts/probes/probe_quarter_mu64_dihedral_sieve.py) (compiling [`probe_quarter_mu64_dihedral_sieve.cpp`](../../../scripts/probes/probe_quarter_mu64_dihedral_sieve.cpp)) runs at **both** independent primes $m = 101$ and $m = 103$ across every Galois orbit of 6-subsets:

| Reflection family | Galois orbits | Verified orbit sum | Max nullity | Total ternary hits (all sizes) | Size-7 hits | Chebyshev $T_8$ positive controls |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| Odd ($c = \zeta_{64}$, 32 nodes) | `28,336` | $\binom{32}{6} = 906,192$ | `2` | `12` | **`0`** | `12 / 12` (all $|A|=|B|=8$) |
| Even ($c = 1$, $C \subset \{1..31\}$) | `47,251` | $\binom{31}{6} = 736,281$ | `3` | `8` | **`0`** | `8 / 8` (all $|A|=|B|=8$) |

Every single ternary kernel vector across all sizes $1 \le d \le 13$ is accounted for by the degree-8 Chebyshev polynomial $T_8(x/2)$ ($12$ odd + $8$ even exact positive controls); **zero** size-7 solutions exist!

## Honesty Boundary

- **Formally proved in Lean (0 `sorry`, axiom-clean):** `QuarterMu64DihedralExclusion.lean` proves all 11 algebraic, score/deficiency-reduction, trace-factorization, Galois-descent, dyadic-cyclotomic-product, norm-lift, modular-kernel-bridge, and prime/orbit headroom theorems (`#print axioms` $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$).
- **Certified by deterministic exact-integer scripts (not yet re-run inside the Lean kernel):**
  - The 31 odd + 109 even exact integer outward-rounded norm enclosures in `probe_quarter_mu64_dihedral_norm.py`,
  - The 16-generator cyclotomic regulator non-vanishing and the 28,336 odd + 47,251 even modular rank checks (at both $m = 101$ and $m = 103$) in `probe_quarter_mu64_dihedral_sieve.py` + `.cpp`.

## Updated Pullback Obstruction Landscape on `[447,392,428, 480,946,858]`

| Inner factor $T$ of a 3-head attack beating `480,946,859` | Status on $p_1$ and $p_2$ | Source |
| :--- | :--- | :--- |
| Any quotient of $\mu_{32}$ or smaller ($x^{2^{25}}$, cyclic or dihedral) | **Eliminated** | `mu32-quarter-list-threshold.md` |
| Any non-dihedral $T$ with $\deg T < 12,463,075$ (and $< 19,173,962$ through `469.76M`) | **Eliminated** | `QuarterIntervalWronskianPullbacks.lean` |
| **Any degree-$2^{25}$ dihedral reflection on $\mu_{64}$ ($c = \zeta_{64}$ or $c = 1$)** | **Eliminated (NEW)** | `QuarterMu64DihedralExclusion.lean` + probes |
| Remaining small-quotient pullbacks | Cyclic $\mu_{64}$ ($x^{2^{24}}$, no reflection symmetry, $m_0 \le 15$) and $\mu_{128}+$ cyclic/dihedral ($x^{2^{23}}$ etc.) | Open |
