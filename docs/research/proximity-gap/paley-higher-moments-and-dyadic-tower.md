# General-Degree Triangular Stepanov–Weil, All-Order Paley Moments, and Dyadic-Tower Laws

This note records six axiom-clean Lean 4 formalizations (`ArkLib/Research/ProximityGap/Frontier/`)
closing the higher-moment CORE Paley/BGK barriers beyond order 4, together with exact dyadic-tower
descent laws, the Mellin–Jacobi factorization of Legendre elliptic traces (with unconditional
coset trace cancellation beating Hasse above $\sqrt{q}/2$), and $k = 5, 6$ switching-class
$\mathbb{F}_3$-rank invariants.

## 1. Lean-Checked Theorems (Zero `sorry`, Zero Custom Axioms)

Every theorem below depends strictly on standard Lean axioms `{propext, Classical.choice, Quot.sound}`
(no external Weil or Deligne axioms).

### 1.1 `HyperellipticStepanov.lean` — General-Degree Triangular Stepanov–Weil Bound
Path: `ArkLib/Research/ProximityGap/Frontier/HyperellipticStepanov.lean`

Previously the repository formalized Stepanov's method only for degree-3 (`cubic`) polynomials
using a uniform condition box (`2√10 ≈ 6.32`, yielding `|S| ≤ 7√q` for large `q` and `13√q`
zero-gap). `HyperellipticStepanov.lean` establishes a **general-degree triangular Stepanov–Weil
engine** for **every** monic squarefree $f \in \mathbb{F}_q[X]$ of **any** positive degree $d$
over **every** odd-characteristic finite field $\mathbb{F}_q$:

- **Graded triangular condition space** `(k : Fin m) × Fin (D + (d - 1) * k + J)` cuts the linear
  constraint count in half (asymptotic constant $2\sqrt{d(d-1)} < 2d - 1$, improving the cubic
  constant from $2\sqrt{10} \approx 6.32$ to $2\sqrt{6} \approx 4.90$).
- **Unified two-sign witness** (`σ = ±1`) bounds both $N^+ = \{s : f(s)^{(q-1)/2} = 1\}$ and
  $N^- = \{s : f(s)^{(q-1)/2} = -1\}$ directly, handling even and odd degrees identically without
  requiring a rational root or quadratic twist.
- **Key theorems**:
  - `linear_charSum_eq_zero`: $\sum_{s \in \mathbb{F}_q} \chi(s - a) = 0$.
  - `quadratic_charSum_eq_neg_one`: $\sum_{s \in \mathbb{F}_q} \chi((s-a)(s-b)) = -1$ ($a \neq b$).
  - `hyperelliptic_stepanov_sq_le` / `hyperelliptic_stepanov_abs_le`:
    $|\sum_{s \in \mathbb{F}_q} \chi(f(s))| \le 4d\sqrt{q}$ for all $d \ge 2$ with **zero small-field gap**.
  - Sharp large-field constants:
    - `hyperelliptic_stepanov_deg3_tight`: $S^2 \le 25 q$ ($|S| \le 5\sqrt{q}$) for $d = 3$, $q \ge 43357$.
    - `hyperelliptic_stepanov_deg4_tight`: $S^2 \le 64 q$ ($|S| \le 8\sqrt{q}$) for $d = 4$, $q \ge 683$.
    - `hyperelliptic_stepanov_deg6_tight`: $S^2 \le 144 q$ ($|S| \le 12\sqrt{q}$) for $d = 6$, $q \ge 1772$.
    - `hyperelliptic_stepanov_deg6_ultra`: $100 S^2 \le 12321 q$ ($|S| \le 11.1\sqrt{q}$) for $d = 6$, $q \ge 10^7 + 1$.
  - `tuple_charSum_abs_le` & `tuple_charSum_oddCard_two`: exact reduction of arbitrary products of
    linear factors $\sum_x \prod_i \chi(x - a_i)$ to squarefree `prodLinear oddSet` plus $\le |\mathrm{evenSet}|$.

### 1.2 `PaleyHigherMoments.lean` — Unconditional All-Order `2r`-th Moments
Path: `ArkLib/Research/ProximityGap/Frontier/PaleyHigherMoments.lean`

- `card_allEven_tuples_le`: at most $(2r - 1)!!\,|T|^r$ tuples in $T^{2r}$ have all-even
  multiplicities.
- `shifted_even_moment_le`: for EVERY odd-characteristic $\mathbb{F}_q$, EVERY $r \ge 1$, and
  EVERY $T \subseteq \mathbb{F}_q$,
  $$\sum_{x \in \mathbb{F}_q} W_T(x)^{2r} \le (2r - 1)!!\,|T|^r q + 9r\,|T|^{2r}\sqrt{q}.$$
- `sum_sq_tupleCharSum_le`:
  $$\sum_{a \in T^{2r}} \Bigl(\sum_{x \in \mathbb{F}_q} \prod_{i=1}^{2r} \chi(x - a_i)\Bigr)^2
    \le (2r - 1)!!\,|T|^r q^2 + 81 r^2\,|T|^{2r} q.$$
- `shifted_sixth_moment_ultra`: for $q \ge 10^7 + 1$,
  $$\sum_{x \in \mathbb{F}_q} W_T(x)^6 \le 15 |T|^3 q + 135 |T|^5 \sqrt{q} + \frac{111}{10} |T|^6 \sqrt{q}.$$

### 1.3 `PaleySubgroupHigherMoment.lean` — Shattering the $|H| \ge q^{1/4}$ Barrier & 18-Bit Production Record
Path: `ArkLib/Research/ProximityGap/Frontier/PaleySubgroupHigherMoment.lean`

- `subgroup_all_poly_power_saving`: breaks the fourth-moment $|H| \ge q^{1/4}$ wall of
  `PaleySubgroupTransversal.lean`. For EVERY $r \ge 1$, EVERY $\eta > 0$, EVERY multiplicative
  subgroup $H$ of arbitrary polynomial size $|H| \ge q^{1/(2r)}$, and EVERY $A \subseteq \mathbb{F}_q^\times$
  with coset occupancy $\le K$ satisfying $2^r((2r-1)!! + 9r) K q^{1/2 + \eta} \le |A||H|$,
  $$|S(A, H)| \le q^{-\eta/(2r)} |A|\,|H|.$$
- `subgroup_even_moment_signed_holder`: generalizes `PaleySubgroupSignedEnergy.fourth_signed_holder`
  from $\ell^{4/3}$ to $\ell^{2r/(2r-1)}$ for every $r \ge 1$.
- **`named_prime_half_sixth` (18-bit / $262{,}144\times$ production-prime improvement)**:
  Using `shifted_sixth_moment_ultra` ($r = 3$, which is the global optimum over all $r \ge 1$ at
  $|H| = 2^{30}, q \approx 2^{159}$), proves $2 |S(A, H)| \le |A|\,|H|$ for EVERY partial
  transversal $A \subseteq \mathbb{F}_q^\times$ of size **`|A| ≥ 2^59`** on **both** designated
  length-$2^{30}$ production primes:
  - $p_1 = 365375409332725729550921208179070755120141565953$ (certificate ratio $0.694 < 1$),
  - $p_2 = 730750818665451459101842416358141509841924915201$ (certificate ratio $0.982 < 1$),
  improving `PaleySubgroupTransversal.named_prime_half` ($|A| \ge 2^{77}$) by 18 bits — and coming
  within **1 bit** of what the full Weil/Deligne bound $|S| \le 5\sqrt{q}$ would give at $r = 3$
  ($|A| \ge 2^{58}$).

### 1.4 `PaleyGramHigherMoment.lean` — All-Order Gram Moments & Simultaneous Inverted-Chart Poles
Path: `ArkLib/Research/ProximityGap/Frontier/PaleyGramHigherMoment.lean`

Closes the written-only $r \ge 3$ higher-moment gap of `paley-cross-ratio-moments.md` axiom-clean:
- `double_even_eq` & `double_even_le`:
  $$\sum_{t, y \in \mathbb{F}_q} \mathrm{gram}(A, t, y)^{2r}
    = \sum_{a \in A^{2r}} (\mathrm{tupleCharSum}(a))^2
    \le (2r - 1)!!\,|A|^r q^2 + 81 r^2\,|A|^{2r} q.$$
- `chart_moment_le_gram`, `partner_even_le`, `exceptionalPoles_le`.
- `exceptionalPoles_power_saving`: shatters the fourth-moment $|A|^2 b_0 \gg q$ ($q^{1/3}$) barrier
  down to **arbitrary polynomial sizes** $|A| \ge q^{1/r}$ and $b_0 \ge q^\eta$, proving
  $$|\mathrm{exceptionalPoles}(A, b_0, |A| q^{-\delta})|
    \le \bigl((2r - 1)!! + 81 r^2\bigr)\, q^{1 - \eta + 2r\delta}.$$

### 1.5 `PaleyDyadicTower.lean` — Exact Antipodal-Pairing and Dyadic-Tower Descent Laws
Path: `ArkLib/Research/ProximityGap/Frontier/PaleyDyadicTower.lean`

Exploits the exact antipodal involution $x \leftrightarrow -x$ and squaring homomorphism
$x \mapsto x^2$ on $-1$-closed nonzero subsets (in particular dyadic subgroups $\mu_{2^m}$):
- `abs_antipodal_pair_eq`: $|\chi(a - x) + \chi(a + x)| = 1 + \chi(a^2 - x^2)$ (holds for EVERY
  odd-characteristic finite field $\mathbb{F}_q$, not just $\chi(-1) = 1$).
- `sq_antipodal_pair_eq`: $(\chi(a - x) + \chi(a + x))^2 = 2 - \mathbf{1}_{a^2 = x^2} + 2\chi(a^2 - x^2)$.
- `dyadic_row_descent` & `dyadic_rectangle_descent`:
  $2 |W_H(a)| \le |H| + 2 W_{H^2}(a^2)$ and $2 |S(A, H)| \le |A||H| + 2 \sum_{a \in A} W_{H^2}(a^2)$.
- `cyclicAuto_half_eq`: for any cyclic subgroup $\langle g \rangle$ of even order $2m$ with
  $g^m = -1$, the half-shift autocorrelation satisfies $R_m(g, 2m) = 2 \sum_{j < m} \chi(1 - g^{2j})$
  (formally explaining the exact production identities $-65858 = 2 \cdot (-32929)$ and
  $-2882 = 2 \cdot (-1441)$).
- `cyclicAuto_descent`: $|R_h(g, 2m)| \le m + R_h(g^2, m) + 2$ for every shift $h$.

### 1.6 `PaleyMellinJacobi.lean` — Mellin–Jacobi Factorization, Deuring–Birch Second Moment, and Coset Trace Cancellation
Path: `ArkLib/Research/ProximityGap/Frontier/PaleyMellinJacobi.lean`

Formalizes the multiplicative harmonic analysis of the Legendre elliptic trace
$L(\lambda) = \sum_{z \in \mathbb{F}_q} \chi(z(z - 1)(z - \lambda))$ completely unconditionally
(zero Gauss-sum, Weil, or Deligne axioms):
- `mellin_jacobi_identity`: for EVERY commutative ring $R$ and EVERY multiplicative map
  $\psi : \mathbb{F}_q^\times \to R$ (including $\psi = 1, \chi$),
  $$\sum_{\lambda \in \mathbb{F}_q^\times} \psi(\lambda)\, L(\lambda) = \chi(-1)\, J(\psi, \chi)^2.$$
- `sum_legendreTrace_eq_zero`, `sum_legendreTrace_qr`, `sum_legendreTrace_nqr`:
  $\sum_{\lambda \in \mathbb{F}_q} L(\lambda) = 0$, $\sum_{\lambda \in \mathrm{QR}} L(\lambda) = \chi(-1)$,
  and $\sum_{\lambda \in \mathrm{NQR}} L(\lambda) = 0$ identically!
- `sum_sq_legendreTrace` & `sum_sq_legendreTrace_punctured`: exact Deuring–Birch second moment
  $\sum_{\lambda \in \mathbb{F}_q} L(\lambda)^2 = q^2 - 2q - 1$ and
  $\sum_{\lambda \neq 0, 1} L(\lambda)^2 = q^2 - 2q - 3$.
- `jacobiSum_norm_sq_eq_card`: $\|J(\psi, \chi)\|^2 = q$ for every nontrivial $\psi \notin \{1, \chi\}$.
- **`abs_sum_coset_legendreTrace_le`**: for EVERY multiplicative subgroup $H \le \mathbb{F}_q^\times$
  and EVERY coset $aH$,
  $$\Bigl|\sum_{\lambda \in aH} L(\lambda)\Bigr| \le q,$$
  strictly beating the trivial Hasse bound $2 |H| \sqrt{q}$ for every subgroup of size $|H| > \sqrt{q}/2$!

---

## 2. Structural & Barrier Findings (Exact Probes — `scripts/probes/probe_paley_higher_moments_and_dyadic.py`)

### 2.1 Cross-Ratio Parseval Coupling, Subgroup Signed Cross-Ratio Energy, and the $k_g$ Barrier
For $A \subseteq \mathbb{F}_p$ of size $n$, let $V_A(\lambda)$ be the signed cross-ratio
multiplicity of distinct ordered 4-tuples $(a, b, c, d) \in A^4$ with cross-ratio
$\lambda = (a - c)(b - d) / ((a - d)(b - c))$, weighted by $\chi(-(a - b)(c - d))$, and set
$\widehat{V_A}(\psi) := \sum_{\lambda \in \mathbb{F}_p^\times} V_A(\lambda) \psi(\lambda)$.
By `PaleyMellinJacobi.mellin_jacobi_identity` (Lean-checked above) and Fourier inversion on
$\mathbb{F}_p^\times$:
$$\langle V_A, L \rangle := \sum_{\lambda \in \mathbb{F}_p^\times} V_A(\lambda)\, L(\lambda)
  = \frac{\chi(-1)}{p - 1} \sum_{\psi} \overline{\widehat{V_A}(\psi)}\, J(\psi, \chi)^2.$$
By `PaleyMellinJacobi.sum_sq_legendreTrace` ($\sum_\lambda L(\lambda)^2 = p^2 - 2p - 1 < p^2$)
and `sum_legendreTrace_eq_zero`, Cauchy–Schwarz yields
$|\langle V_A, L \rangle| \le p \sqrt{\sum_{\lambda} (V_A(\lambda) - \bar{V}_A)^2}$.
Comparing with the two target scales:
- **Beating pointwise Hasse ($2 n^4 \sqrt{p}$)** requires
  $\sum_\lambda (V_A(\lambda) - \bar{V}_A)^2 \ll n^8 / p$.
- **Breaking $p^{1/2}$ for a single subgroup row sum $W_H(a)$**: since $W_H(ua)^4 = W_H(a)^4$ on
  cosets of $H$, $n W_H(a)^4 \le \sum_x W_H(x)^4 \le 3 n^2 p + |\langle V_H, L \rangle| + O(n^3)$,
  so $|W_H(a)| = o(n)$ follows whenever $|\langle V_H, L \rangle| \ll n^5$, i.e.,
  $\sum_\lambda V_H(\lambda)^2 \ll n^{10} / p^2$. Since $V_H(\lambda) = n M_H(\lambda)$ for a
  subgroup $H$, this asks for signed cross-ratio energy $E_{\mathrm{cr}}^{\mathrm{signed}}(H)
  = \sum_\lambda M_H(\lambda)^2 \ll n^8 / p^2$.
- **Exact $p$-sweep finding**: across $p \in [101, 3329]$ with $n \approx \sqrt{p}$, the empirical
  signed energy satisfies $E_{\mathrm{cr}}^{\mathrm{signed}}(H) / n^3 \in [3.9, 6.9]$ (whereas
  unsigned bounds via intersection sizes $k_g = |H \cap g^{-1} H|$ give only
  $\sum_\lambda V_H(\lambda)^2 \ll n^6$, yielding $p \sqrt{n^6} = p n^3 \ge n^5$ for all
  $n \le p^{1/2}$). Any unconditional proof of $E_{\mathrm{cr}}(H) \ll n^{4 - \delta}$ immediately
  breaks the $p^{1/2}$ single-row subgroup barrier down to $n > p^{1/(2 + \delta/2)}$ (and
  $O(n^3)$ reaches $p^{2/5}$).

### 2.2 Complete $k = 5, 6$ Switching-Class $\mathbb{F}_3$-Rank Classification (Negative Result)
Extending `paley-four-site-rank.md` beyond $k = 4$, exact enumeration of all canonical switching
classes of $k \times k$ zero-diagonal $\{\pm 1\}$ matrices ($e = \chi(-1) \in \{\pm 1\}$) shows:
- **$k = 5, e = -1$ ($p \equiv 3 \pmod 4$)**: **64/64 (100%)** of switching classes have
  $\mathrm{rank}_{\mathbb{F}_3} = 4$. Thus the 5-site $\mathbb{F}_3$-rank is identically constant
  and carries zero discriminating power for $p \equiv 3 \pmod 4$.
- **$k = 5, e = +1$ ($p \equiv 1 \pmod 4$)**: $\mathrm{rank}_{\mathbb{F}_3}$ distribution is
  $\{4: 42,\; 5: 22\}$ (64 classes).
- **$k = 6, e = -1$**: $|\mathrm{Pf}| \in \{1, 3, 5, 7, 9\}$ (always odd, hence never zero over
  $\mathbb{Q}$); $\mathrm{rank}_{\mathbb{F}_3}$ distribution is $\{4: 280,\; 6: 744\}$ (1024 classes).
- **$k = 6, e = +1$**: $\mathrm{rank}_{\mathbb{F}_3}$ distribution is $\{4: 210,\; 5: 90,\; 6: 724\}$ (1024 classes).

### 2.3 Verification Command
```bash
python3 scripts/probes/probe_paley_higher_moments_and_dyadic.py
```
