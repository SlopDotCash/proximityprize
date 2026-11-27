# Complete Elimination of ALL Toric-Supported Pencils on $\mu_{64}$, $\mu_{128}$ (Both Designated Primes) & Across the Infinite Dyadic Tower

## Summary

This note accompanies [`QuarterToricPencilExclusion.lean`](../../../ArkLib/Research/ProximityGap/Frontier/QuarterToricPencilExclusion.lean) and [`probe_quarter_toric_pencil.py`](../../../scripts/probes/probe_quarter_toric_pencil.py).

A **toric-supported pencil** on $\mu_N$ ($N = 2^k$) is any coprime polynomial pair
$$P(z) = z^{a_0} L_A(z), \qquad Q(z) = z^{b_0} L_B(z) \qquad (A, B \subset \mu_N\text{ disjoint},\; a_0 = 0 \lor b_0 = 0,\; m = \max(a_0 + |A|,\; b_0 + |B|) < N/4)$$
whose finite zeros lie in $\mu_N \cup \{0\}$ — allowing **arbitrary unequal support sizes $|A| \ne |B|$** and arbitrary missing roots at $0$ and $\infty$. Because `mu64-unit-lattice-transfer.md` and `mu128-unit-ellipsoid-transfer.md` raise ratio comparisons to the $64$-th / $128$-th power (cancelling any root-of-unity phase $z^{a_0 - b_0}$!), **every** toric-supported ratio comparison lifts identically from BOTH designated primes $p_1$ and $p_2$ to $\mathbb{C}$.

## Main Results

1. **Exact Toric Unit-Circle Phase Law (`toric_unit_circle_phase_power_eq_one`, `toric_nonzero_phase_root_cap`, `toric_odd_diff_at_most_one_root`):**
   On $S^1 \subset \mathbb{C}$, for any disjoint $A, B \subset S^1$ and any $a_0, b_0 \in \mathbb{Z}$, whenever $z^{a_0} L_A(z) / (z^{b_0} L_B(z))$ takes the same value at $z_1, z_2 \in S^1 \setminus (A \cup B)$:
   $$\left(\frac{z_2}{z_1}\right)^{2(a_0 - b_0) + (|A| - |B|)} = 1.$$
   Setting $K := 2(a_0 - b_0) + (|A| - |B|)$:
   - If $K \ne 0$, then $|C| \le |K|$ (roots of $X^{|K|} - 1$); if $|A| \not\equiv |B| \pmod 2$ on $\mu_{2^k}$, then $K$ is odd, forcing **$|C| \le 1$**!

2. **Zero-Search Elimination of ALL Nonzero-Phase Toric Pencils (`toric_nonzero_phase_score_le_deg`):**
   Whenever $K \ne 0$ and $|C| \le |K|$, we have $|A| + |B| + |C| \le 2 m$, capping the three-head score at
   $$2(|A| + |B| + |C|) - 3 m \le m < \frac{N}{4} \ll \frac{9}{16} N.$$
   Thus EVERY toric-supported pencil beating `480,946,859` must satisfy exact phase balance $2(a_0 - b_0) + (|A| - |B|) = 0$ (WLOG $b_0 = 0, |B| = |A| + 2 a_0$).

3. **Zero-Search Infinite-Tower Exclusion ($N = 2^k \ge 128$, including $\mu_{128}$ over BOTH $p_1$ and $p_2$):**
   - **Even-shift antipodal descent ($a_0$ even, $A = -A, B = -B$):** descends to a toric-supported pencil on $\mu_{N/2}$ with degree $m/2$ and score $S/2$.
   - **Odd-shift antipodal descent impossible (`toric_odd_shift_antipodal_descent_impossible`):** when $a_0 \ge 1$ is odd and $A, B$ are antipodal on $\mu_N$, $|\tilde{B}| - |\tilde{A}| = a_0$ is odd, so $\tilde{A}, \tilde{B}$ cannot be antipodal on $\mu_{N/2}$; beating `480,946,859` forces $|\tilde{C}| \ge \frac{5}{16}(N/2) + 4$, so Depth 2 on $\mu_{N/2}$ immediately gives $|\tilde{C}_{0 \bmod 4}| \ge \frac{5}{16}(N/2) > (N/2)/4$ — instant pigeonhole contradiction for ALL $N \ge 128$!
   - **Non-descending case (`toric_stripped_antipodal_poly_ne_zero`, `toric_non_descending_depth3_contradiction`):** proves $G'(X) = X^{a_0} A_0(X) B_0(-X) - (-X)^{a_0} A_0(-X) B_0(X) \ne 0$ for any $a_0 \in \mathbb{N}$ and forces $|C| \le N/8 < \frac{5}{32} N + 1$ for ALL $N \ge 128$!

4. **Complete $\mu_{64}$ Partial-Head Toric Classification (`mu64_all_toric_partial_profiles_classification`):**
   Among ALL phase-balanced toric tuples on $\mu_{64}$ ($m \le 15$, $r_A < m \lor r_B < m$, $r_C \le \max(a_0 + r_A, b_0 + r_B)$) beating score `36`:
   - Every equal-size profile (`(14,14,14)`, `(14,14,13)` at $m = 15$) forces $a_0 = b_0 = 0$ and collapses to $m = 14$ two-full-head (already eliminated by Milestone 6);
   - Every $r_C = m$ case (`(14,14,12)` at $m=14$, `(15,15,13)` and `(15,15,11)` at $m=15$) has two full heads ($\{B, C\}$ or $\{A, C\}$ of degree $m \in \{14, 15\}$, already eliminated by Milestone 6);
   - The **sole** genuinely $\le 1$-full-head unequal toric family is **`m = 15`, `{rA, rB} = {13, 15}`, `{a₀, b₀} = {1, 0}`, `rC ∈ {13, 14}`** (profiles `(15, 13, 13)` and `(15, 14, 13)`), which cannot descend ($13, 15$ odd) and forces $|C_{0 \bmod 4}| \ge 9$ inside $\mu_{16}$. [`probe_quarter_toric_pencil.py`](../../../scripts/probes/probe_quarter_toric_pencil.py) exhausts all `111` orbits of $\binom{16}{9} = 11{,}440$ (and even all `111` orbits of $\binom{16}{7} = 11{,}440$) with **ZERO weight constraint** ($\sum w$ unconstrained!) at both $m = 101$ and $m = 103$, certifying `ternary_non_anti = 0` (at $k = 9$, `max_null = 6`, 111/111 orbits have zero non-antipodal vectors in their entire $\mathbb{Q}$-kernel!).

## Honesty Boundary

- **100% axiom-clean Lean (`QuarterToricPencilExclusion.lean`):** All 8 public theorems are proved with Mathlib-only imports, 0 `sorry`, 0 warnings, and `#print axioms` $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$.
- **Written transfer & Python verification:** The lift of toric ratio comparisons from exact $p_1$ and $p_2$ to $\mathbb{C}$ uses the written transfer bounds in `mu64-unit-lattice-transfer.md` and `mu128-unit-ellipsoid-transfer.md` (which raise ratios to the $64$-th/$128$-th power, cancelling any $z^{a_0 - b_0}$ phase), and the finite `μ_{16}` orbit exhaustion for `rC ∈ {13, 14}` is verified deterministically by `probe_quarter_toric_pencil.py`.
- **Remaining $\mu_{64}$ / $\mu_{128}$ boundary:** Given the written transfer and orbit exhaust, every toric-supported pencil (arbitrary unequal degrees, arbitrary roots at $0$ and $\infty$, zero symmetry assumed) is eliminated on $\mu_{64}$ and $\mu_{128}$ over BOTH $p_1$ and $p_2$ (and across the entire infinite tower in char 0). On $\mu_{64}$ and $\mu_{128}$, ONLY genuinely non-toric partial pencils where at least two heads have finite nonzero roots strictly outside $\mu_N \cup \{0\}$ remain open!
