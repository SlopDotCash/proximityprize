# General Depth-$L$ Dyadic Fourier Parity Theorem & Elimination of Two-Full-Head Cyclic $\mu_{64}$ / $\mu_{128}$ Pullbacks

## Summary

This note accompanies [`QuarterMu64Mu128CyclicExclusion.lean`](../../../ArkLib/Research/ProximityGap/Frontier/QuarterMu64Mu128CyclicExclusion.lean) and [`probe_quarter_mu64_mu128_cyclic.py`](../../../scripts/probes/probe_quarter_mu64_mu128_cyclic.py) (+ [`probe_quarter_mu64_anti_deg15.cpp`](../../../scripts/probes/probe_quarter_mu64_anti_deg15.cpp)).

We prove a **general Depth-$L$ Dyadic Fourier Parity Theorem** (`depthL_fourier_parity_zero`, valid over any field with a primitive $2^k$-th root of unity and $\operatorname{char} \nmid 2^k$, for arbitrary depth $1 \le L \le k - 2$):
- **$L = 1$ ($3$ centres in $0 \bmod 2$):** recovers the classic Three-Centre Parity Lemma (`DyadicParityLemma.lean`).
- **$L = 2$ ($5$ centres in $0 \bmod 4$):** simultaneously forces antipodal invariance on $2 \bmod 4$ and quarter-turn invariance on odd indices.
- **$L = 3$ ($9$ centres in $0 \bmod 8$):** simultaneously forces antipodal invariance on $4 \bmod 8$, quarter-turn invariance on $2 \bmod 4$, and eighth-turn invariance on odd indices.

Combining Depth 1–3 with a 3-line stripped antipodal polynomial bound (`stripped_antipodal_poly_ne_zero`, `depth3_antipodal_pair_ceiling`) yields four immediate consequences:

1. **Complete Infinite-Tower Characteristic-Zero Exclusion ($N = 2^k \ge 32$):** Zero two-full-head quarter-rate pencils beating `480,946,859` ($|A| = |B| = m_0 < N/4$, $m_0 + 2|C| > 9N/16$, **no symmetry assumed**) exist on $\mu_{2^k}$ for **every** $k \ge 5$ ($\mu_{32}, \mu_{64}, \mu_{128}, \mu_{256}, \dots, \mu_{2^{30}}, \dots$). Every $N \ge 128$ collapses purely algebraically by induction on $k$ with **zero computer search**.
2. **Unconditional Elimination of ALL Two-Full-Head Cyclic $\mu_{64}$ and $\mu_{128}$ Pullbacks on BOTH Designated Primes $p_1$ and $p_2$:** Combining with the exact finite-field-to-complex ratio transfers of [`mu64-unit-lattice-transfer.md`](mu64-unit-lattice-transfer.md) and [`mu128-unit-ellipsoid-transfer.md`](mu128-unit-ellipsoid-transfer.md) eliminates **100% of all two-full-head cyclic $\mu_{64}$ ($m_0 \le 15$) and $\mu_{128}$ ($m_0 \le 31$) pullbacks** beating `480,946,859` on both $p_1$ and $p_2$ — with **no symmetry assumption whatsoever**.
3. **Complete Elimination of Anti-Invariant Degree-15 Reflections on $\mu_{64}$:** Eliminates $P(z) = (z+1) z^7 U(z+1/z)$, $Q(z) = (z-1) z^7 V(z+1/z)$ (where $R(1/z) = -R(z)$) over both $p_1$ and $p_2$ (pure-integer $\mathbb{Q}(\zeta_{64})^+$ norm bound $< 2^{151} < p_1 < p_2$ + `consistent = 0` across all `47,251` orbits of $\binom{31}{6} = 736{,}281$ at both $m = 101, 103$).
4. **Sharpened Characteristic-Zero Full Split-Pencil Floor (`char0_full_split_eighth_floor`):** Improves the characteristic-zero full $(d, d, d)$ split-pencil descent floor on $\mu_{2^k}$ ($k \ge 7$) from $3N/16$ down to **$N/8 - 2$**.

## Proof Overview

### 1. General Depth-$L$ Dyadic Fourier Parity Theorem (`depthL_fourier_parity_zero`)

Fix $N = 2^k$ and depth $1 \le L \le k - 2$. Suppose $f_0, \dots, f_{L-1} : \mathbb{Z}/N\mathbb{Z} \to K$ are supported on the $L$ dyadic shells $v_2(y) = L - 1 - j$ and satisfy antiperiodicity $f_j(y + N/2^{j+1}) = -f_j(y)$. Suppose the symmetric odd-generator sum
$$S(x, r) = \sum_{j=0}^{L-1} \big(f_j(x + 2^{L-1-j} r) + f_j(x - 2^{L-1-j} r)\big)$$
is independent of $x$ across a set $C \subseteq \{x \in \mathbb{Z}/N\mathbb{Z} : 2^L \mid x\}$ of size $|C| \ge 2^L + 1$.

For any odd integer $u$, taking the $2^{L-1} u$-th Fourier coefficient over all odd $r$ via fiberwise multiplicity counting (`sum_odds_shell_shift`) yields the degree-$2^L$ Laurent identity in $T = \zeta^{u x}$:
$$K_u = \sum_{j=0}^{L-1} 2^{L-1-j} \big(\hat{f}_j(2^j u) T^{-2^j} + \hat{f}_j(-2^j u) T^{2^j}\big).$$
Multiplying by $T^{2^{L-1}}$ gives a polynomial $P_u \in K[X]$ of degree $\le 2^L$ vanishing at the $|C| \ge 2^L + 1$ distinct nonzero points $T = \zeta^{u x}$ ($x \in C$). Hence $P_u = 0$ identically, forcing $\hat{f}_j(2^j u) = 0$ for every odd $u$ and every $j < L$. Antiperiodicity (`antiperiodic_hat_eq_zero`) kills all remaining frequencies $\omega$, so discrete Fourier inversion forces $f_j \equiv 0$ identically.

### 2. Stripped Antipodal Polynomial & Infinite-Tower Induction (`N = 2^k ≥ 128`)

Assume inductively that no two-full-head quarter-rate pencil beating `480,946,859` exists on $\mu_{N/2}$ (base cases: $\mu_{32}$ via `mu32-quarter-list-threshold.md`, $\mu_{64}$ below). On $\mu_N$ ($N \ge 128$), beating `480,946,859` forces $|C| \ge \frac{5}{32} N + 1 \ge 21$ (`tower_ge_128_depth3_contradiction`):
- **Depth 1 ($3$ centres):** If $|C_{\text{even}}|, |C_{\text{odd}}| \ge 3$, both $A, B$ are antipodal $\implies$ descends to $\mu_{N/2}$, contradiction. Otherwise WLOG $|C_{\text{odd}}| \le 2$, $|C_{\text{even}}| \ge 19$, and $A_{\text{odd}}, B_{\text{odd}}$ are antipodal.
- **Depth 2 ($5$ centres):** If $|C_{0 \bmod 4}|, |C_{2 \bmod 4}| \ge 5$, applying `depthL_fourier_parity_zero` ($L = 2$) on both cosets forces $A = -A, B = -B \implies$ descends to $\mu_{N/2}$, contradiction. Otherwise WLOG $|C_{2 \bmod 4}| \le 4$; Depth 2 fixes $L_A, L_B, \lambda$ under $\zeta_N \mapsto i\zeta_N$, forcing $4 \mid |C_{\text{odd}}| \le 2 \implies C_{\text{odd}} = \emptyset$ and $|C_{0 \bmod 4}| \ge 17$.
- **Depth 3 ($9$ centres):** Split $|C_{0 \bmod 4}| = |C_{0 \bmod 8}| + |C_{4 \bmod 8}| \ge 17$. If both $\ge 9$, Depth 3 on both forces $A = -A, B = -B \implies$ descends to $\mu_{N/2}$. Otherwise WLOG $|C_{0 \bmod 8}| \ge 9$; Depth 3 forces $A, B, C$ to be antipodally invariant everywhere outside $0 \bmod 8$.
- **Universal $\frac{N}{8} - 2$ ceiling:** Stripping antipodal pairs from $A_0, B_0 \subset \mu_{N/8}$ yields coprime non-antipodal $A'_0, B'_0$ with $|A'_0| \equiv |B'_0| \pmod 2$ and $G'(X) = A'_0(X) B'_0(-X) - A'_0(-X) B'_0(X) \ne 0$ (`stripped_antipodal_poly_ne_zero`). Because $G'(0) = 0$ and leading terms cancel, $G'$ has at most $|A'_0| + |B'_0| - 2$ nonzero roots, yet vanishes on all of $C_{\text{out}}$ and all $CC$ antipodal pairs in $C_{0 \bmod 8}$. Over the $N/16$ antipodal pairs of $\mu_{N/8}$, `depth3_antipodal_pair_ceiling` yields
  $$|C| \le \frac{N}{8} - 2 < \frac{5}{32} N + 1 \le |C|, \qquad \text{contradiction!}$$

### 3. Base Case $\mu_{64}$ (`mu64_case2B_forces_seven_in_mu16`) & Anti-Invariant Deg-15

On $\mu_{64}$, Depth 1 & Depth 2 force either descent to $\mu_{32}$ (impossible) or $C_{\text{odd}} = \emptyset$, $|C_{2 \bmod 4}| \le 4$, $|C_{0 \bmod 4}| \ge 7$ inside $\mu_{16}$, with $A_{\text{odd}}, B_{\text{odd}}$ quarter-turn invariant and $A_{2 \bmod 4}, B_{2 \bmod 4}$ antipodal. `probe_quarter_mu64_mu128_cyclic.py` exhausts all `111` rotation+Galois orbits of 7-subsets of $\mu_{16}$ (verified sum $\binom{16}{7} = 11{,}440$) at both $m = 101$ and $m = 103$, finding **`0` non-antipodal solutions**.

For the anti-invariant degree-15 reflection $P(z) = (z+1) z^7 U(z+1/z)$, $Q(z) = (z-1) z^7 V(z+1/z)$ on $\mu_{64}$, `probe_quarter_mu64_mu128_cyclic.py` certifies (pure exact integer arithmetic) $|N_{\mathbb{Q}(\zeta_{64})^+/\mathbb{Q}}(1 - \rho)| < 2^{151} < p_1 < p_2$ on all 109 Galois-representative interior pairs, and `probe_quarter_mu64_anti_deg15.cpp` certifies **`0` consistent systems** across all `47,251` orbits of $\binom{31}{6} = 736{,}281$ at both $m = 101$ and $m = 103$.

## Honesty Boundary

- **100% axiom-clean Lean (`QuarterMu64Mu128CyclicExclusion.lean`):** Proves `depthL_fourier_parity_zero` (full general Depth-$L$ Fourier theorem), `stripped_antipodal_poly_ne_zero`, `depth3_antipodal_pair_ceiling`, `tower_ge_128_depth3_contradiction`, `char0_full_split_eighth_floor`, `mu64_case2B_forces_seven_in_mu16`, `mu64_anti_deg15_forces_eleven`, and `cyclic_and_anti_prime_headroom` with 0 `sorry`, 0 warnings, and `#print axioms` $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$.
- **Deterministic scripts + prior transfer certificates:** Finite-field-to-complex ratio transfer on $\mu_{64}$ and $\mu_{128}$ uses `mu64-unit-lattice-transfer.md` / `mu128-unit-ellipsoid-transfer.md`; the 111-orbit $\mu_{64}$ Case 2B check and the anti-invariant deg-15 integer norm + 47,251-orbit sieve are verified by `probe_quarter_mu64_mu128_cyclic.py` + `.cpp`.
- **Remaining pullback boundary on `[447,392,428, 480,946,858]`:** On $\mu_{64}$ and $\mu_{128}$, ONLY partial three-head pencils where **at least two heads have roots outside $\mu_N$** (e.g. $(14, 13, 13)$ or $(15, 14, 12)$ on $\mu_{64}$, which are not monic $\mu_N$-vanisher ratios) remain open; every two-full-head cyclic pullback on $\mu_{32}, \mu_{64}, \mu_{128}$, every dihedral reflection on $\mu_{64}$, every anti-invariant deg-15 reflection on $\mu_{64}$, every dyadic eigenspace pullback across $\mu_{64}\dots\mu_{2^{30}}$, and every non-dihedral inner factor of degree $< 12{,}463{,}075$ are now eliminated on both $p_1$ and $p_2$.
