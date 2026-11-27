# Wave 2 CORE Paley Results: Signed Square-Root Engine, Four-Site $\mathbb{F}_3$-Rank Ceilings, and Cross-Ratio / Spectral Barriers

This note records the Wave 2 CORE Paley/BGK advances formalized axiom-clean in Lean 4 (`#print axioms` strictly $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$, zero `sorry`) together with their exact Python verification probe.

## 1. Structural Barriers & Exact Spectral Laws (`PaleyCrossRatioBarrier.lean`)

File: [`ArkLib/Research/ProximityGap/Frontier/PaleyCrossRatioBarrier.lean`](../../../ArkLib/Research/ProximityGap/Frontier/PaleyCrossRatioBarrier.lean) (Mathlib-only, 8 audited public theorems):

1. **Exact quartic-to-Legendre cross-ratio reduction (`quartic_charSum_eq_legendreTrace`)**:
   For every odd-characteristic finite field $\mathbb{F}_q$ and every four distinct $a,b,c,d\in\mathbb{F}_q$,
   $$
     \sum_{x\in\mathbb{F}_q}\chi\!\big((x-a)(x-b)(x-c)(x-d)\big)
     \;=\; -1 + \chi\big(-(a-b)(c-d)\big)\,L\!\left(\frac{(a-c)(b-d)}{(a-b)(c-d)}\right),
   $$
   where $L(\lambda)=\sum_{z\in\mathbb{F}_q}\chi(z(z-1)(z-\lambda))$.

2. **Unsigned Cross-Ratio Energy Barrier (`sum_unsignedCrossRatioCount`, `unsigned_crossRatio_energy_ge`, `unsigned_cauchy_schwarz_cannot_beat_hasse`)**:
   For every finite field $\mathbb{F}_q$ and every subset $A\subseteq\mathbb{F}_q$ of size $n$, let $V_A^{\mathrm{un}}(\lambda)$ count ordered distinct 4-tuples in $A$ with cross-ratio $\lambda\in\mathbb{F}_q\setminus\{0,1\}$. Then
   $$
     (q-2)\sum_{\lambda\ne 0,1}V_A^{\mathrm{un}}(\lambda)^2 \;\ge\; \big(n(n-1)(n-2)(n-3)\big)^2,
   $$
   and hence
   $$
     q\sqrt{\sum_{\lambda\ne 0,1}V_A^{\mathrm{un}}(\lambda)^2}
     \;\ge\; \sqrt{q}\cdot n(n-1)(n-2)(n-3).
   $$
   **Consequence (refuted proof path):** Bounding the 4th-moment off-diagonal inner product $|\langle V_A^{\mathrm{signed}}, L\rangle|$ via Cauchy–Schwarz + $|V_A^{\mathrm{signed}}(\lambda)|\le V_A^{\mathrm{un}}(\lambda)$ and $\sum L(\lambda)^2 < q^2$ can **never** beat the pointwise Hasse scale $\sqrt{q}\cdot(n)_4$ for *any* set $A$ of *any* size (including multiplicative subgroups $\mu_n$). Breaking the $\sqrt{p}$ wall via $\langle V_A^{\mathrm{signed}}, L\rangle$ strictly requires either internal sign cancellation inside $V_A^{\mathrm{signed}}(\lambda)$ or phase cancellation between the Mellin transform $\widehat{V_A^{\mathrm{signed}}}(\psi)$ and the squared Jacobi sum $J(\psi,\chi)^2$.

3. **Exact Dyadic-Tower DFT Even/Odd Parseval Energy Split (`dyadic_dft_even_energy`, `dyadic_dft_odd_energy`)**:
   For any cyclic subgroup $\langle g\rangle\le\mathbb{F}_q^\times$ of even order $2m$ ($g^m=-1$) and cyclic Paley sequence $c_j=\chi(1-g^j)$, the DFT $\widehat{c}(k)=\sum_{j=0}^{2m-1}c_j e^{2\pi i k j/(2m)}$ satisfies
   $$
     \sum_{r=0}^{m-1}|\widehat{c}(2r)|^2 \;=\; m\big(2m-1+2s(H^2)\big),\qquad
     \sum_{r=0}^{m-1}|\widehat{c}(2r+1)|^2 \;=\; m\big(2m-1-2s(H^2)\big),
   $$
   where $s(H^2)=\sum_{j=0}^{m-1}\chi(1-(g^2)^j)$ is the cyclic Paley sum of the index-2 square subgroup $H^2$.

4. **Five-Site Skew-Symmetric $\mathbb{F}_3$-Rank Constancy (`skew_five_f3_exists_nonzero_minor`, `skew_five_f3_rank_eq_four`)**:
   Every $5\times 5$ skew-symmetric zero-diagonal $\{\pm 1\}$ matrix over $\mathbb{F}_3$ has `Matrix.rank M = 4` identically: $\det M = 0$ by odd-dimensional skew symmetry, and at least one of the three principal $4\times 4$ minors dropping index $2,3,$ or $4$ is always nonzero (pure algebra over $\mathbb{F}_3$ via the $4\times 4$ Pfaffian identity).
   **Consequence (refuted proof path):** Unlike 4-site $\mathbb{F}_3$-rank (`paley-four-site-rank.md`), 5-site $\mathbb{F}_3$-rank carries zero discriminating power for primes $p\equiv 3\pmod 4$.

## 2. Full Lean Formalization of the Arbitrary-Sign Square-Root Engine (`paley-signed-square-root.md`)

Previously, `docs/research/proximity-gap/paley-signed-square-root.md` existed only as a written proof + finite Python check. Wave 2 formalizes the entire finite and asymptotic signed theory cleanly across three modular, axiom-clean Lean files:

### 2.1 `PaleySignedHankelDegree.lean`
File: [`ArkLib/Research/ProximityGap/Frontier/PaleySignedHankelDegree.lean`](../../../ArkLib/Research/ProximityGap/Frontier/PaleySignedHankelDegree.lean)
- **`signedDet_ne_zero_and_natDegree_le`**: Column-reversal + unit-diagonal upper-triangular transform + falling-factorial Vandermonde + suffix-preserving echelon degree reduction proves that for EVERY odd prime $p$, EVERY $A\subseteq\mathbb{F}_p$ with $2\le|A|\le (p-1)/2+1$, EVERY individual vertex sign assignment $w_u\in\{\pm 1\}$ ($u\in A$), and EVERY width $1\le x\le \lfloor |A|/2\rfloor$, the normalized Hankel determinant `signedDet A w (x - 1)` is nonzero and has degree at most the sharp minority-corrected budget
  $$
    D_x \;=\; x(d + a - 2x) - (x-s)_+(a-x-s)_+,
  $$
  where $s = \min(\#\{u\in A:w_u=1\},\#\{u\in A:w_u=-1\})$.

### 2.2 `PaleySignedSquareRoot.lean`
File: [`ArkLib/Research/ProximityGap/Frontier/PaleySignedSquareRoot.lean`](../../../ArkLib/Research/ProximityGap/Frontier/PaleySignedSquareRoot.lean)
- **`signed_local_dvd`** and **`signed_row_estimate`**: Proves the exact finite row budget
  $$
    \sum_{t\in\mathbb{F}_p}\big(W_w(t)^2 - (|A| - z_t - 2x)^2\big)_+ \;\le\; 4 D_x.
  $$
- **`sum_sq_signedShiftSum`**, **`sum_signed_central_multiplicity`**, **`signed_central_factorization`**, and **`signed_central_rootMultiplicity`**: Proves exact shift orthogonality $\sum_t W_w(t)^2 = p|A| - (\sum_{u\in A} w_u)^2$ and the complete arbitrary-sign central polynomial factorization at $x = \lfloor |A|/2\rfloor$:
  $$
    \det J \;=\; \operatorname{lc}(\det J)\prod_{t\in\mathbb{F}_p}(X-t)^{\lfloor W_w(t)^2/4\rfloor}.
  $$
- **`signed_rectangle_sq_le_exact`**, **`signed_rectangle_sq_le`**, **`signed_discrepancy_65537`**, and **`eventually_signed_balanced_discrepancy`**:
  - Concrete finite certificate: for EVERY $A, B \subseteq \mathbb{F}_{65537}$ of size $256$ and EVERY vertex signs $w, v\in\{\pm 1\}$, $|\sum_{u\in A, t\in B} w_u v_t \chi(u-t)| \le 56{,}829$.
  - Asymptotic arbitrary-sign balanced bound: for any sequence of primes $p_n\to\infty$ with $|A_n|,|B_n|\sim\sqrt{p_n}$ and arbitrary vertex signs $w_n, v_n$, eventually $|S(A_n,B_n;w_n,v_n)| / (|A_n||B_n|) < \sqrt{3}/2 + \varepsilon$.

### 2.3 `PaleyFourSiteRankAndOverlap.lean`
File: [`ArkLib/Research/ProximityGap/Frontier/PaleyFourSiteRankAndOverlap.lean`](../../../ArkLib/Research/ProximityGap/Frontier/PaleyFourSiteRankAndOverlap.lean)
- **`four_site_energy_le`**: Proves the explicit finite Gram-energy ceiling $E(X,X) \le U_x = n\big((n-1)(n-2-2x)^2+(n-1-2x)^2+4x(d+n-1-2x)\big)$ for $3\le n\le d+2$, $1\le x\le\lfloor(n-1)/2\rfloor$.
- **`energy_eq_four_site_singular`**: Proves the exact 4-site ternary-rank identity
  $$
    E(X,X) \;=\; n(n-1)(2n-3) + 8\chi(-1)\!\left(4N_4(X) - \binom{n}{4}\right).
  $$
- **`four_site_singular_le_mod1`**, **`four_site_singular_65537`**, and **`eventually_four_site_singular_density_mod1`**:
  - Concrete certificate: every 256-site set $X\subseteq\mathbb{F}_{65537}$ has at most $142{,}536{,}640$ singular 4-subsets modulo $3$ (out of $\binom{256}{4}=174{,}792{,}640$).
  - Asymptotic bound: for $p_n\equiv 1\pmod 4$ and $|X_n|\sim\sqrt{p_n}$, eventually $N_4(X_n)/\binom{|X_n|}{4} < 13/16 + \varepsilon$.
- **`skew_sum_diag_zero`** and **`skew_overlap_discrepancy_le`**: Proves both the diagonal-cancellation bound $|S|\le |A||B|-|C|^2$ and the sharp Cauchy–Schwarz overlap bound for $p\equiv 3\pmod 4$, which strictly beats $\sqrt{3}/2$ whenever the relative overlap $\theta=|A\cap B|/m$ lies in $(1-\sqrt{3}/2,1)$.

## 3. Honesty Boundary & Exact Reproduction

- **Kernel-checked in Lean 4** (zero `sorry`, zero custom axioms): every theorem named in §1–§2 above (`PaleyCrossRatioBarrier.lean`, `PaleySignedHankelDegree.lean`, `PaleySignedSquareRoot.lean`, `PaleyFourSiteRankAndOverlap.lean`).
- **Remaining open in `paley-signed-square-root.md`** (written-only, not yet formalized in Lean): the Balog–Szemerédi–Gowers + Chang + Pollard near-extremizer additive-energy reduction (§"Additive energy in every chart of a near-extremizer", lines 90–107 of `paley-signed-square-root.md`) and the signed pair-product identity (lines 65–71).
- **Exact verifier probe**: run `python3 -B scripts/probes/probe_paley_wave2_cross_ratio_and_signed.py` (5 exact test suites covering all finite identities, the $p=65537$ constants, and exhaustive 64/64 switching-class verification of 5-site skew $\mathbb{F}_3$-rank constancy).
