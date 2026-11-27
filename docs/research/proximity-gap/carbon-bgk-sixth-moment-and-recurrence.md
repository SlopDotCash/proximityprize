# Production Sixth-Moment Laws, Cross-Coset Sextuple Obstructions, and Finite-Window Holonomic Recurrence Bounds

**Module:** `ArkLib/Research/ProximityGap/Frontier/CarbonBGKSixthMomentAndRecurrence.lean`  
**Probe / Style Audit:** `scripts/probes/probe_carbon_bgk_sixth_moment.py`  
**Honesty Status:** Unconditional theorems + exact algebraic reductions (zero `sorry`, zero new `axiom`; standard `{propext, Classical.choice, Quot.sound}` only).

---

## 1. Overview of Results

This note and companion Lean 4 module formalize four core results on the sixth Gauss-period moment (`r = 3`) over dyadic multiplicative subgroups $H = \mu_n \subset \mathbb{F}_p^\times$ ($n = 2^{30}$), advancing the analytic sixth-moment frontier on warm canonical substrate imports (`SubgroupGaussSumMoment`, `DCSubtractedMoment`, `GaussPeriodCosetReduction`, `_PrizeShapePrimeP30`, `_PrizeShapePrimeP30Second`):

1. **Exact Normalized-Pair Decomposition of `rEnergy H 3`, Subgroup Divisibility, DC-Moment Equivalence, and Exact $u = 1$ Multiplicity (`§1`):**
   - **`rEnergy_three_eq_normProfile` & `card_dvd_rEnergy_three`**: Connects `SubgroupGaussSumMoment.rEnergy H 3` directly to the normalized pair-signature histogram $m(u) = \#\{(x, y) \in H^2 : (1 + x + y)^n = u\}$ via
     $$E_3(H) = (n\,m(0))^2 + n \sum_{u \ne 0} m(u)^2,$$
     and deduces exact subgroup divisibility $n \mid E_3(H)$.
   - **`dcSixthMoment_le_wick_iff_rEnergy_le`**: Using `DCSubtractedMoment.sum_nonzero_moment` and $n \mid E_3(H)$, proves that for every finite field with $|F| > n^5$ (including both designated primes $P_1, P_2$ and every prime in $[2^{158}, 2^{159}]$), the DC-subtracted sixth-moment Wick bound is **equivalent** to the integer energy ceiling:
     $$\sum_{b \ne 0} \|\eta_b\|^6 \le 15\,|F|\,n^3 \iff E_3(H) \le 15\,n^3.$$
   - **`normProfile_one_ge_three_card_sub_three` & `normProfile_one_eq_of_sidon`**: Proves unconditionally that for even $n > 0$ in odd characteristic, the three antipodal families $(-1, y)$, $(x, -1)$, and $(x, -x)$ contribute **at least $3n - 3$** pairs to the $u = 1$ bin ($3n - 3 \le m(1)$), with **exact equality $m(1) = 3n - 3$** whenever $H$ satisfies the weak Sidon law (`a + b = c + d → a + b = 0 ∨ a = c ∨ a = d`).

2. **$2.5\times$ Sharper Unconditional Production Occupied-Bin Floor via $u = 1$ Puncturing (`§2`):**
   - `NormalizedTraceRecurrenceWidth.production_min_bins` bounded the number of occupied signature bins $d = |\mathrm{occupied}(H, 2^{30})|$ by Cauchy–Schwarz across *all* bins without removing the giant singleton spike $m(1) \ge 3n - 3$ (which alone carries $n(3n - 3)^2 \approx 9n^3$ of the $15n^3$ energy!), yielding only $d \ge \lceil n^2 / 15 \rceil = 76{,}861{,}433{,}640{,}456{,}466$.
   - **`punctured_one_occupancy_bound` & `production_punctured_min_bins`**: Applying Cauchy–Schwarz on $U_1 = \mathrm{occupied}(H, n) \setminus \{1\}$ gives
     $$n\,(n^2 - m(1))^2 \le |U_1|\,(E_3(H) - n\,m(1)^2),$$
     and the exact algebraic monotonicity identity for $t = m(1) \ge t_0 := 3n - 3$:
     $$(6n^2 + 18n - 9)(n^2 - t)^2 - (n^2 - 3n + 3)^2(15n^2 - t^2) = (t - t_0)\Big[6n^2(n - 6)(n^2 - 3n + 3) + \big((6n^2 + 18n - 9) + (n^2 - 3n + 3)^2\big)(t - t_0)\Big] \ge 0$$
     proves—**under the exact same hypotheses $E_3(H) \le 15n^3$, without needing `FourTermConditions` or $A_5 + 2A_6$**—that
     $$|\mathrm{occupied}(H, 2^{30})| \ge 192{,}153{,}582{,}490{,}528{,}435 \quad (\text{and } |\mathrm{occupied}(H, 2^{30}) \setminus \{0\}| \ge 192{,}153{,}582{,}490{,}528{,}434),$$
     improving the $76{,}861{,}433{,}640{,}456{,}466$ bound by a factor of **$2.5\times$** ($\approx n^2 / 6$ vs $n^2 / 15$).

3. **Finite-Window Polynomial-Coefficient (Holonomic) Recurrence Lower Bound (`§3`):**
   - Formalizes in Lean 4 the finite-difference propagation proof (`PROGRESS.md` entry on polynomial-coefficient recurrences over the finite modular coefficient window $0 \le j \le (p - 1)/n$):
   - **`finite_window_poly_recurrence_degree`**: Let $U \subseteq \mathbb{F}_p^\times$ be a set of nonzero nodes with nonzero weights $w(u) \ne 0$, and let $S_k = \sum_{u \in U} w(u)\,u^k$. If polynomials $A_0, \dots, A_r \in \mathbb{F}_p[X]$ of degree $\le b < p$ (not all zero) annihilate $S$ on the **finite initial window**
     $$\sum_{i=0}^r A_i(j)\,S_{j+i} = 0 \quad \text{for all } 0 \le j < |U|\,(b + 1),$$
     then **$|U| \le r$**.
   - **Proof architecture:** Representing the left-shift operator as `shiftEnd : Module.End F (ℕ → F)` and evaluating $\prod_{u \in U} (X - u)^{b+1}$ via `Polynomial.aeval`, binomial finite differencing kills each $u^j Q_u(j)$ globally on $\mathbb{N}$; monicity of degree $|U|(b + 1)$ propagates the finite-window zeros to all $j \in \mathbb{N}$; choosing $a \in \mathbb{F}_p$ with $A_{i_0}(a) \ne 0$ (`b < p`) and sampling along the arithmetic progression $j = a + p k$ (`u^{p} = u`) forces $\sum_{i=0}^r A_i(a) X^i \ne 0$ to vanish on all of $U$ by Vandermonde invertibility.
   - **`production_holonomic_window_recurrence_degree`**: Specializes to $H = \mu_{2^{30}} \subset \mathbb{F}_p^\times$ at any prime $p > 2^{150}$ (including $P_1, P_2$, where $|U|(b + 1) + r \le 2^{120} + 2^{61} < (p - 1)/2^{30}$ for all $r, b \le 2^{60}$): under the unit sixth-moment Wick bound, every nonzero polynomial-coefficient recurrence of degree $b < p$ valid on the initial $|U|(b + 1)$ offsets must have order
     $$r \ge 192{,}153{,}582{,}490{,}528{,}434.$$

4. **Cross-Coset `2+2+2` S-Unit / Sidon Reduction and $\mu_4$-Coset Occupancy Elimination (`§4`):**
   - **`crossCoset_two_two_two_sunit`, `pair_signature_inv_eq`, & `crossCoset_two_two_two_sidon_cap`**: Any cross-coset `2+2+2` zero-sum sextuple $a_1(1 + u_1) + a_2(1 + u_2) + a_3(1 + u_3) = 0$ ($a_j \in \mu_n$, $u_j \in \mu_m$) collapses to the normalized two-root line $(1 + u_1) z_1 + (1 + u_2) z_2 + (1 + u_3) = 0$. Since $(1 + u^{-1})^n = (1 + u)^n$, whenever $(1 + u_1)^n = (1 + u_2)^n$ (including equal or inverse $K$-gaps) and $\mu_n$ is weak-Sidon with $1 + u_1 \ne 0, 1 + u_3 \ne 0$, at most **two** normalized cross-coset solutions $(z_1, z_2) \in \mu_n^2$ can exist.
   - **`quarterCoset_occupancy_at_least_five`**: For any antipode-free 6-element zero-sum subset $S \subseteq \mu_n$ ($2 \mid n$, $i^2 = -1, i^n = 1$) satisfying the two-disjoint-quarter-pair exclusion, every $\mu_4$-coset contains at most $2$ elements of $S$ and at most one $\mu_4$-coset contains $2$ elements, forcing **at least $5$ distinct $\mu_4$-cosets** (`5 ≤ (S.image (· ^ 4)).card`)—eliminating `6`, `5+1`, `4+2`, `4+1+1`, `3+3`, `3+2+1`, `2+2+2`, and `2+2+1+1` and leaving only `2+1+1+1+1` and `1+1+1+1+1+1`.
