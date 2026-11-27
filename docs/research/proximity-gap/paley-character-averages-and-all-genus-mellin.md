# Character Averages with Prescribed First Set and All-Genus Mellin–Jacobi Theory

This note records two axiom-clean Lean 4 formalizations (`#print axioms` strictly $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$, zero `sorry`, zero external Weil/Deligne axioms) advancing the CORE Paley/BGK analytic substrate:

## 1. Complete Character Averages with a Prescribed First Set (`PaleyCharacterAverages.lean`)

File: [`ArkLib/Research/ProximityGap/Frontier/PaleyCharacterAverages.lean`](../../../ArkLib/Research/ProximityGap/Frontier/PaleyCharacterAverages.lean) (Mathlib-only, 6 audited public theorems, formalizing [`paley-character-averages.md`](paley-character-averages.md)):

Let $\mathbb{F}_q$ be any finite field, $A \subseteq \mathbb{F}_q$ any prescribed subset of size $m$, and $W_\psi(b) = \sum_{a \in A} \psi(a + b)$ (with $\psi(0) = 0$) over the cyclic group of $q - 1$ multiplicative characters $\psi$ of $\mathbb{F}_q^\times$ (`exists_dlog`).

1. **All-order complete character-averaged $2r$-th moment (`sum_mulChar_even_moment_le`)**:
   For every $r \ge 1$,
   $$
     \sum_{\psi} \sum_{b \in \mathbb{F}_q} |W_\psi(b)|^{2r}
     \;\le\; (q - 1)\bigl(r!\,q\,m^r + (r - 1)\,m^{2r}\bigr).
   $$
2. **Exact complete & nonprincipal fourth moments (`sum_all_mulChar_fourth_moment_eq`, `sum_nonprincipal_fourth_moment_eq`, `sum_nonprincipal_fourth_moment_le`)**:
   Writing $E_+(A) = \#\{(u,v,w,z)\in A^4 : u + v = w + z\}$,
   $$
     \sum_{\psi \ne 1} \sum_{b \in \mathbb{F}_q} |W_\psi(b)|^4
     \;=\; (q - 1)\bigl(q(2m^2 - m) - 4m^3 + 4m^2 - m - E_+(A)\bigr) + m(m - 1)(3m^2 - 3m + 1)
     \;\le\; (q - 1)\,q\,(2m^2 - m).
   $$
3. **Exceptional-character fraction over all partners $|B| \ge |A|$ (`card_bad_characters_le`)**:
   For every nonempty $A \subseteq \mathbb{F}_q$ ($|A| = m \ge 1$), every $r \ge 1$, and every $\rho > 0$, the fraction of multiplicative characters $\psi$ admitting *any* partner $B \subseteq \mathbb{F}_q$ with $|B| \ge m$ and $\bigl|\sum_{b \in B} W_\psi(b)\bigr| \ge \rho\,m|B|$ is at most
   $$
     \rho^{-2r}\!\left(\frac{r!\,q}{m^{r+1}} + \frac{r - 1}{m}\right).
   $$

## 2. All-Genus Mellin–Jacobi Factorization & Cross-Ratio Parseval Barrier (`PaleyAllGenusMellinJacobi.lean`)

File: [`ArkLib/Research/ProximityGap/Frontier/PaleyAllGenusMellinJacobi.lean`](../../../ArkLib/Research/ProximityGap/Frontier/PaleyAllGenusMellinJacobi.lean) (imports `PaleyMellinJacobi`, 6 audited public theorems):

For any odd-characteristic finite field $\mathbb{F}_q$ and any $m \in \mathbb{N}$ (genus $\lfloor m / 2 \rfloor$), define the $m$-parameter hyperelliptic Legendre trace
$$
  L_m(\lambda_0, \dots, \lambda_{m-1})
  \;=\; \sum_{z \in \mathbb{F}_q} \chi\!\left(z(z-1)\prod_{j=0}^{m-1}(z - \lambda_j)\right).
$$

1. **Exact All-Genus Mellin–Jacobi Factorization (`all_genus_mellin_jacobi_identity`)**:
   For every commutative ring $R$ and every $m$-tuple of functions $\psi_j : \mathbb{F}_q \to R$ multiplicative on $\mathbb{F}_q^\times$,
   $$
     \sum_{\lambda \in (\mathbb{F}_q^\times)^m}
       \left(\prod_{j=0}^{m-1} \psi_j(\lambda_j)\right) L_m(\lambda)
     \;=\; \chi(-1)\,J\!\left(\chi^{m+1}\prod_{j=0}^{m-1} \psi_j,\,\chi\right)
           \prod_{j=0}^{m-1} J(\psi_j, \chi).
   $$
2. **Exact 1-Variable Sliced Mellin–Jacobi Factorization (`sliced_mellin_jacobi_identity`)**:
   Fixing any $\lambda_0, \dots, \lambda_{m-1} \in \mathbb{F}_q$ and Mellin-transforming in one parameter $\mu \in \mathbb{F}_q^\times$ still factorizes identically into
   $$
     \sum_{\mu \in \mathbb{F}_q^\times} \psi(\mu)\,L_{m+1}(\lambda, \mu)
     \;=\; J(\psi, \chi) \sum_{z \in \mathbb{F}_q^\times}
           \psi(z)\,\chi\!\left((z-1)\prod_{j=0}^{m-1}(z-\lambda_j)\right).
   $$
3. **Exact All-Genus Deuring–Birch $L^2$ Moment (`sum_sq_hyperellipticTrace_eq`)**:
   For every odd-characteristic $\mathbb{F}_q$ and every $m \in \mathbb{N}$,
   $$
     \sum_{\lambda \in \mathbb{F}_q^m} L_m(\lambda)^2
     \;=\; (q - 2)(q - 1)^m + (-1)^m (3 - q).
   $$
   (Specializes at $m = 1$ to $q^2 - 2q - 1$.)
4. **Unconditional All-Genus Product-Coset Trace Cancellation (`sq_sum_product_coset_hyperellipticTrace_le`)**:
   For every family of subgroups $H_0, \dots, H_{m-1} \le \mathbb{F}_q^\times$ and coset shifts $a_j \in \mathbb{F}_q^\times$,
   $$
     \left(\sum_{u \in \prod_j H_j} L_m(a_0 u_0, \dots, a_{m-1} u_{m-1})\right)^2
     \;\le\; q^{m+1}.
   $$
   For subgroups of size $|H_j| = K > \sqrt{q}$, this beats pointwise Weil $(m+1)K^m\sqrt{q}$ unconditionally by a factor $\sim (K / \sqrt{q})^m$ with zero Weil/Deligne axioms.
5. **Sharp Cross-Ratio Parseval Crossover Barrier (`subgroup_crossRatio_parseval_barrier`, `production_parseval_barrier_all_r`)**:
   By $H$-scaling invariance, any $(2r - 3)$-cross-ratio multiplicity table on $H^{2r}$ ($|H| = n$, total mass $T$) is supported on at most $n^{2r-1}$ active orbits, forcing unsigned energy $E \ge T^2 / n^{2r-1}$. Whenever $n^{2r-1} \le q^{2r-3}$ (i.e., $\log_q(n) \le \frac{2r-3}{2r-1}$: $1/3$ at $r=2$, $3/5$ at $r=3$, $5/7$ at $r=4$), we have $T^2 q \le q^{2r-2} E$, so raw higher-genus cross-ratio Parseval against the Deuring–Birch $L^2$ scale $q^{r-1}$ can **never** beat the pointwise Weil scale $T\sqrt{q}$. In particular, for the Proximity Prize smooth subgroup $n = 2^{30}$ and any prime $q \ge 2^{158}$, `(2^30)^(2r-1) ≤ q^(2r-3)` holds for **every** $r \ge 2$ — proving thin-regime subgroup cancellation ($\alpha \approx 0.189$) must come from direct $x$-domain arguments rather than higher-genus cross-ratio Parseval.

## 3. Honesty Boundary & Exact Probes

- **Kernel-checked in Lean 4** (zero `sorry`, zero custom axioms): all 6 public theorems in `PaleyCharacterAverages.lean` and all 6 public theorems in `PaleyAllGenusMellinJacobi.lean`.
- **Exact probes**:
  - `python3 -B scripts/probes/probe_paley_character_average.py` (exact nonprincipal fourth moments verified on 2,212 prescribed domains).
  - `python3 -B scripts/probes/probe_paley_all_genus_mellin_jacobi.py` (Deuring–Birch exact $L^2$ across $m \in \{0,1,2,3\}$, 165 all-genus Mellin–Jacobi checks, 40 sliced checks, 185 product-coset checks, and production Parseval barrier across $r = 2..100$).
