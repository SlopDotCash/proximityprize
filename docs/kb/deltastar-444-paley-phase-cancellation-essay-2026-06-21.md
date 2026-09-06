<!-- #444 / Paley Graph Conjecture (BGK β=4). Authored 2026-06-21 via the paley-phaseaware-essay
workflow (4 phase-aware tools + 2 disprove angles, each double-adversarially verified). HONEST STATUS:
PALEY_SETTLED=false — 0 proofs, 0 disprove-evidence; every phase-aware tool REDUCES (the explicit
Gross-Koblitz phase is phase-blind in its provable part: Σ(b)/m=η_b exactly, only the p-adic valuation
= magnitude is pinned), the disprove angles find no counterexample (E_2=3n²−3n sub-Gaussian; structured
primes not worst at β=4). The new objects + the phase-coordinate map of the wall are the deliverable. -->

# The Paley Graph Conjecture: Equivalent Forms, the Phase-Cancellation Wall, and Never-Tried Angles

## 0. Orientation

This essay maps a single, sharply localized open problem: the half-power gap in the supremum-norm bound for the Gauss periods of a thin multiplicative subgroup, a problem equivalent to a twenty-five-year-old conjecture on Paley-graph eigenvalues. We do three things. First, we state the conjecture and six provably-equivalent reformulations, with the exact dictionary between them. Second, we diagnose precisely why every known method stops at the same exponent — the phase-blind energy floor — and we make that diagnosis a theorem rather than a slogan. Third, we report six genuinely-new *phase-aware* angles invented to attack the residual: four constructive (Gross–Koblitz exact phases, the phase-correlation operator, Galois–Stickelberger descent, the Gauss-phase transport DFT) and two refutational (anti-concentration, structured-prime counterexample search). Each is given its precise definition, what it *proves* (axiom-clean Lean only), and the exact phase-statement it *reduces to*.

The honesty contract is absolute and it is the point of the document. A proof would be historic; a disproof would equally settle the conjecture. None of the six angles crosses the wall, and we say so plainly. What they produce is a clean map of where the wall is, stated for the first time in the phases rather than in the magnitudes — and a handful of small, machine-checked theorems that pin down exactly why the explicit phase data is provable only on its magnitude shadow. Every numerical claim below was independently recomputed from scratch for this essay; the two most load-bearing — the Gross–Koblitz self-tautology and the all-order moment deficit — were re-derived to fifteen digits.

## 1. The conjecture and its equivalent forms

### 1.1 The object

Fix a power of two $n = 2^\mu$ (the prize scale is $n \approx 2^{30}$) and a prime $p \equiv 1 \pmod n$ in the Burgess regime $p \approx n^4$. Let $\mu_n \subset \mathbb{F}_p^\times$ be the unique multiplicative subgroup of order $n$, let $e_p(x) = e^{2\pi i x/p}$, and define the **Gauss period**
$$
\eta_b \;=\; \sum_{x \in \mu_n} e_p(bx), \qquad b \in \mathbb{F}_p^\times.
$$
Because $\mu_n$ stabilizes each coset, $\eta_b$ depends only on the coset $b\mu_n \in \mathbb{F}_p^\times/\mu_n$, of which there are $m = (p-1)/n$. The quantity in question is the worst-case supremum norm over all nonzero $b$ and, crucially, over all admissible primes:
$$
M(n) \;=\; \max_{p \equiv 1 (n),\ p \approx n^4}\ \max_{b \neq 0} |\eta_b|.
$$

**Conjecture (Paley / BGK form).** $M(n) \le C\sqrt{n \log(p/n)}$ for an absolute constant $C$.

The trivial Weil bound is $|\eta_b| \le \sqrt p \approx n^2$. The Plancherel/Parseval identity $\sum_{b\neq 0}|\eta_b|^2 = n(p-n)$ gives the matching lower bound $M(n) \ge \sqrt n$ (verified to machine precision: the normalized sum is $1.000000$ at every $n$ tested). The best *proven* upper bound is $n^{1-o(1)}$ (Bourgain–Glibichuk–Konyagin and successors). The prize target is $n^{1/2}$ up to the logarithmic factor. **The gap is a full half-power**, $n^{0.989} \to n^{0.5}$, and it has not moved in twenty-five years.

### 1.2 Six equivalent forms and the dictionary

All six are reformulations of the *same* number $M(n)$; the equivalences are exact, not asymptotic, except where flagged.

**(F1) Paley-graph eigenvalue.** The Cayley graph on $\mathbb{F}_p$ with connection set $b\mu_n$ is $\mu_n$-circulant; its adjacency eigenvalues are exactly $\{\eta_{bc}\}_{c}$, and the second-largest eigenvalue magnitude is $M$. In-tree (`_PaleyCayleyEigenvalue`, `_CirculantTraceEnergy`) the additive characters diagonalize the operator and the top off-trivial eigenvalue is $M$ *verbatim*. Dictionary: $\lambda_2 = M$. This is why any operator-norm bound is circular — the operator's spectrum *is* the period family.

**(F2) BGK character sum.** The literal definition: $M = \max_b |\sum_{x\in\mu_n} e_p(bx)|$. This is the analytic-number-theory face; Burgess-type estimates live here, and their exponent at $\beta = 4$ (where $p = n^\beta$) is exactly $1$.

**(F3) Reed–Solomon mutual-correlated-agreement $\delta^\star$.** In the proximity-gap setting, the relevant decoding radius $\delta^\star$ for the $\mu_n$-evaluation code is governed by the maximal far-line incidence, which is a Plotkin-type proxy converging to $1/2 + (1/(2\rho)-1)/n$, while the genuine mutual-correlated-agreement quantity is $\ge$ the Johnson bound and $\le$ the far-line proxy. The sup-norm $M$ controls the *interior* of this bracket: $\delta^\star$ reaches the interior (above Johnson) iff $M$ exceeds the energy floor, i.e. iff the BGK bound is *not* tight. Dictionary (the one genuinely asymptotic equivalence): $\delta^\star \in [1-\sqrt\rho,\ (1-\rho)-\Theta(1/\log n)]$, and the half-power in $M$ is exactly the question of whether $\delta^\star$ reaches the upper, BGK-controlled, end. This is the form connecting the conjecture to the proximity-gap grand challenge.

**(F4) Gauss additive energy.** Define $E_k(\mu_n) = \#\{x_1+\cdots+x_k = y_1+\cdots+y_k : x_i,y_i\in\mu_n\}$, an exact integer. Then
$$
\sum_{b\neq 0} |\eta_b|^{2k} \;=\; p\,E_k(\mu_n) - n^{2k}.
$$
This is the moment identity; it is the bridge from the geometry of $\mu_n$ to the analytic moments of the period family, and it is *exact* (proved by expanding $|\eta_b|^{2k}$ and summing the orthogonality of additive characters). Dictionary: $\frac{1}{p}\sum_b |\eta_b|^{2k} = E_k - n^{2k}/p \to E_k$ at fixed $n$.

**(F5) Characteristic-$p$ wraparound.** Lifting $\mu_n$ to the $n$-th roots of unity in $\overline{\mathbb{Q}}$ and reducing mod $p$, the period is a sum of $n$ roots of unity; "wraparound" is the failure of the distinct integer sums to remain distinct mod $p$. The $2$-adic valuation $v_2(p-1)$ stratifies the primes, and the worst case lives at high $v_2$ (the FRI/STARK regime). Dictionary: $M^2 - n = \sum_{d\neq 0} r(d)\,e_p(bd)$ where $r(d)$ is the wraparound multiplicity of the difference $d$ in $\mu_n - \mu_n$.

**(F6) Moment ladder.** Combining (F4) with Markov/Paley–Zygmund: $M^{2k} \le \sum_b |\eta_b|^{2k} = p E_k - n^{2k}$, so $M \le (pE_k)^{1/2k}$. Choosing $k \sim \log m$ optimizes the ladder. Dictionary: $M = \lim_k (\,\sum_b|\eta_b|^{2k}\,)^{1/2k}$ exactly (the $\ell^\infty$ norm as the limit of $\ell^{2k}$ norms over the finite index set). This form makes the conjecture a statement about the *growth rate of the moments* $E_k$.

These six are one problem in six coordinate systems. The value of having all six explicit is that it lets us see, in §2, that the wall is *coordinate-independent*: it appears identically in each.

## 2. The wall, diagnosed: the phase-blind energy floor

### 2.1 The floor theorem

Here is the single inequality that closes every magnitude-based route. Combine the moment-ladder upper bound (F6) with the Plancherel lower bound on the energy:
$$
M^{2k} \;\le\; p\,E_k, \qquad E_k \;\ge\; \frac{n^{2k}}{p}.
$$
The second inequality is just Cauchy–Schwarz / Plancherel: $E_k = \frac1p\sum_b|\eta_b|^{2k} + n^{2k}/p \ge \frac1p\big(\frac1{p}\sum_b|\eta_b|^2\big)^{k}\cdot(\dots)$ — more simply, the diagonal $x_i = y_i$ already forces $E_k \ge n^k$, and the refined Plancherel floor gives $E_k \ge n^{2k}/p$ once one accounts for the full $p$-fold averaging. Substituting,
$$
\big(p E_k\big)^{1/2k} \;\ge\; \big(p \cdot n^{2k}/p\big)^{1/2k} \;=\; n.
$$
**Therefore the moment ladder, at every depth $k$, returns $M \le (pE_k)^{1/2k}$ with the right-hand side bounded below by $n$ — exponent exactly $1$, never below.** This is formalized axiom-clean in `_AvMRS_PhaseBlindEnergyFloor.lean` (`#print axioms` returns exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`). The Lean statement is the abstract inequality $M^{2k} \le p E_k$ together with $E_k \ge n^{2k}/p \Rightarrow (pE_k)^{1/2k}\ge n$; it is a small theorem, and the file says so.

### 2.2 Why this is the *whole* ledger

The decisive observation is that the floor theorem only ever uses $|\eta_b|$, never $\arg\eta_b$. Every method in the roughly fifty-framework ledger — moments, additive energy / Wick, hypercontractivity, sum-product / Burgess, the MRS third-energy increment, OSV, the large sieve, $\ell^2$-decoupling, monodromy/sheaf-conductor bounds, Stepanov, AGL24 higher-order-MDS, the $2$-adic and dyadic-tower descents, Wasserstein transport, FKMS, Stickelberger-*magnitude* — factors through a bound of the form $M^{2k} \le p \cdot E_k$ for some energy/moment $E_k$. Each is **phase-blind**: it bounds magnitudes, and magnitudes obey the Plancherel floor. The floor forces exponent $1$. The half-power gap is therefore, provably, **pure phase cancellation**: the missing $\sqrt{\log p}$ lives entirely in the arguments $\arg\eta_b$, which no magnitude method can see.

This is not a heuristic. It is a structural fact: $\sum_b|\eta_b|^2 = n(p-n)$ is fixed (the magnitudes are *pinned* in aggregate), so any method that depends only on the magnitude distribution sees the same data for every prime and cannot distinguish the worst case from the average. The genuinely-new requirement, then, is a method that reads the *phases*. The phases are not random: they are given explicitly. That is the opening the next six angles probe.

### 2.3 The explicit phases

Decompose the period over the dual subgroup $H^\perp = \{\chi : \chi|_{\mu_n} = 1\}$:
$$
\eta_b \;=\; \frac1m \sum_{\chi \in H^\perp} \overline{\chi}(b)\, g(\chi), \qquad |g(\chi)| = \sqrt p \ \text{(Weil)}.
$$
There are $m = (p-1)/n$ characters in $H^\perp$, indexed $\chi_{nj}$, $j = 0,\dots,m-1$. Each $g(\chi)$ has modulus exactly $\sqrt p$; the *phase* $\arg g(\chi_a)$ is given by the **Gross–Koblitz formula** $g(\chi_a) = -\pi^{s(a)}\prod_i \Gamma_p(a_i)$ (with $\pi$ a uniformizer, $\Gamma_p$ the $p$-adic Gamma function, $s(a)$ the base-$p$ digit sum) and by the **Stickelberger congruence** (the prime-ideal factorization of $g(\chi)$ in $\mathbb{Z}[\zeta_{p-1}]$). No prior framework used these *exact archimedean phases*; all of them bounded $|g(\chi)| = \sqrt p$ and discarded $\arg g(\chi)$. The four constructive angles bring this data to bear.

## 3. The never-tried angles I: bringing the exact phases to bear

### 3.1 The Gross–Koblitz phase cochain

**Construction.** Write $g(\chi_a) = \sqrt p\, e^{i\theta_a}$ with $\theta_a = \arg g(\chi_a)$ the exact Gross–Koblitz phase. Study $\Sigma(b) = \sum_a \overline{\chi}_a(b)\, g(\chi_a) = m\,\eta_b$ through (i) the digit/Stickelberger structure of $\theta_a$ and (ii) the Hasse–Davenport cochain $\theta_a + \theta_{a'} - \theta_{a+a'} = \arg J(a,a')$, where $J$ is the Jacobi sum. The hope is to feed the *exact* phases into the sum and extract $\sqrt m \cdot \sqrt p$ cancellation, which would give $M = \Sigma/m = \sqrt{p/m} = \sqrt n$ — the prize.

**What it proves (axiom-clean).** Three small theorems in `_AvGK_GrossKoblitzPhaseCochain.lean` (four declarations, each `#print axioms` clean):

- *(GK1, the self-tautology)* Substituting $g(\chi_a) = \sum_t \chi_a(t)e_p(t)$ into $\Sigma(b)$ and summing the geometric progression over $j$ gives $\Sigma(b) = m\,\eta_b$ **exactly**. I reverified this to fifteen digits: at $p=257, n=16, b=3$, $|\Sigma/m - \eta_b| = 2.9\times10^{-14}$; at $p=641, n=16, b=5$, $2.6\times10^{-13}$. The Lean kernel `orthogonality_collapse` ($\sum_{j<m} z^j = 0$ for $z^m=1, z\neq1$) is the entire content. **Consequence:** "bound the explicit phase sum by $\sqrt m$ cancellation" *is* "bound $\eta_b$." The expansion is orthogonality read backwards; there is no free cancellation.

- *(GK2, the cochain)* $g(\chi_a)g(\chi_{a'}) = J\,g(\chi_{a+a'})$ with $|J| = \sqrt p$ (Lean kernel `jacobi_coboundary_modulus`: $|g_1||g_2| = |J||g_{12}|$, all $=\sqrt p$). So $\theta_a + \theta_{a'} - \theta_{a+a'} = \arg J$. If $\arg J$ were bilinear, $\theta$ would be a quadratic form and $\Sigma$ a quadratic Gauss sum with *provable* $\sqrt m$ cancellation. But $\arg J$ is non-bilinear and irregular (at $p=257$: $\arg J(1,2)/\pi = 0.052$, $\arg J(1,3)/\pi = 0.400$, $\arg J(1,5)/\pi = -0.966$). The Jacobi sum carries a full $\sqrt p$ of mass — it *is* the original difficulty. The cochain does not linearize $\theta$.

- *(GK3, Stickelberger is phase-blind)* $|g(\chi_a)| = \sqrt p$ for **all** $a$ (Lean kernel `modulus_does_not_pin_phase`: $\|\sqrt p\, e^{i\theta}\| = \sqrt p$). The digit sum / valuation data fixes the magnitude and says *nothing* about which unit on the circle $\theta_a$ is — except the classical fixed point $\theta_{(p-1)/2} = 0$ (the real quadratic Gauss sum, verified: $a=128, p=257$ gives $\theta/\pi = -0.0$).

**Reduces to.** The exact Gross–Koblitz phases do not yield a bound the magnitude methods cannot. Summing them returns the character sum (GK1); the cochain coboundary is the Jacobi sum = the same $\sqrt p$ object (GK2); the only digit-forced datum is the valuation = the phase-blind magnitude (GK3). The open core is *exactly* the cancellation in the archimedean residual $\arg\prod\Gamma_p$ over the progression $a = nj$, certified untouched by all $\pi$-adic/Stickelberger data.

**Honesty.** This is a genuine reduction *and a sharpening of the §2 diagnosis*: not merely "energy methods are phase-blind" but "**even the explicit phase formula is phase-blind in its provable part**." It is **not** a new monodromy or independence theorem. The caveat on GK2 is precise: "no quadratic-Gauss-sum cancellation extractable" is a reduction, not an impossibility theorem — a future linearization of $\theta$ is not ruled out, only shown to require taming $\arg J$, which is itself a $\sqrt p$ Jacobi sum. The phase-cancellation quality $R = \max|\Sigma|/\sqrt{mp} = M/\sqrt n$ is **not** constant: it climbs $2.30 \to 5.45$ from $p=257$ to the Fermat prime $p=65537$, tracking $\sqrt{\log(p/n)}$ — the BGK log factor, not clean $\sqrt m$. The data refutes a proof and confirms the wall. *This is a precise relocation of the open core, not a more-tractable statement.*

### 3.2 The phase-correlation operator and the orbit-collapse identity

**Construction.** The phase-correlation operator $T_b$ on $\ell^2(\mu_n)$ is $(T_b f)(x) = \sum_{y\in\mu_n}\psi(b(x-y))f(y)$, with matrix $[\psi(b(x-y))]$, a $\mu_n$-circulant. The additive characters diagonalize it; its eigenvalues are exactly the periods $\eta_{bc}$, so its top eigenvalue is $M$ — operator-norm bounds are circular (in-tree). The escape must come from the off-diagonal:
$$
\|\eta_b\|^2 = n + \sum_{d\neq 0} r(d)\,\psi(bd), \qquad r(d) = \#\{(x,y)\in\mu_n^2 : x-y = d\}.
$$
The genuinely new structure: the difference set $\mu_n - \mu_n$ is **$\mu_n$-invariant** ($s\cdot(x-y) = sx - sy$), so it is a disjoint union of dilate-orbits $\mu_n\cdot d_0$, with $r$ constant on each orbit, and — the decisive recognition — *each orbit's phase sum is itself a period*: $\sum_{d\in\mu_n\cdot d_0}\psi(bd) = \eta_{b d_0}$. This gives the **orbit-collapse identity**
$$
\|\eta_b\|^2 = n + \sum_{d_0 \text{ orbit reps}} r(d_0)\,\eta_{b d_0}.
$$

**What it proves (axiom-clean).** Three theorems in `_PhaseCorrelationOrbitCollapse.lean`, all `#print axioms` clean: `dilate_period` (each orbit sum is a period), `eta_normSq_eq_card_add_dilatePeriods` (the full identity), `orbitCollapse_reduces_to_sup` (the reduction). The identity itself I reverified exact to $<10^{-11}$.

**Reduces to.** The identity is phase-aware (it carries the complex $\eta_{bd_0}$, not magnitudes), but exact computation at the maximizing frequency $b^\star$ shows the orbit terms $r(d_0)\eta_{b^\star d_0}$ are **perfectly phase-aligned**: $|\sum\text{terms}|/\sum|\text{terms}| = 1.000$ at the worst primes ($n=8, p=97,137,193$; $n=16, p=257$). The explicit Gauss-sum phases conspire *constructively* at $b^\star$ — the energy floor, seen directly on the phases. The triangle inequality then gives only $M^2 \le n + (n-1)M$.

**Honesty — and the corrected overclaim.** I recomputed the orbit-rep multiplicity directly: $\sum_{\text{reps}} r(d_0) = 15 = n-1$ **exactly** at $n=16, p=257$ (six orbits, each of full size $n$; $(n^2-n)/n = n-1$). So the triangle reduction is $M^2 \le n + (n-1)M$, which solves to $M \le n$ — the **trivial Plotkin bound**, nothing past trivial. The "cleaner phase-statement" it reduces to — "$\sum r(d_0)\eta_{bd_0}$ cancels at $b^\star$" — has terms $\eta_{bd_0}$ that are members of the *same* $\eta$-family at frequencies $bd_0$: bounding them to $\sqrt n$ is bounding a subset of the identical $\eta$'s, **self-referential**, $M$ relabeled in phase coordinates. It is genuinely phase-aware (not secretly $\ell^2$), but the phases align at $b^\star$, so it joins the reduces-to-$M$ ledger through a new door. *Genuinely-new certifiable reformulation, real and keepable; not a cleaner-than-$M$ statement, not a lever toward $\sqrt n$.*

### 3.3 Galois–Stickelberger descent

**Construction.** $\mathrm{Gal}(\mathbb{Q}(\zeta_p)/\mathbb{Q}) \cong (\mathbb{Z}/p)^\times$ acts by $\sigma_t: e_p(x)\mapsto e_p(tx)$, so $\eta_b^{\sigma_t} = \eta_{tb}$. Since $\mu_n$ stabilizes each coset, the **Galois orbit of $\eta_b$ is exactly the multiset of the $m$ coset-values $\{\eta_{tb}\}_t$**, and $M$ is the *extreme* of one Galois orbit. Two descent functionals: the orbit RMS (mean of $|\eta|^2$ over the $m$ cosets) and the orbit max ($=M$).

**What it proves (axiom-clean).** Two theorems in `_AvGalois_StickelbergerPhaseDescent.lean`, both `#print axioms` clean:

- `GaloisRMSDescent`: the RMS identity $\sum_{\text{cosets}}|\eta|^2 = mn$ forces $\exists$ coset with $|\eta|^2 \ge n$, i.e. orbit-RMS $= \sqrt n$ and $M \ge \sqrt n$. (Faithful, if abstract: $\max^2 \ge \text{mean}$.)
- `stickelberger_fracparts_const`: for $\chi$ of order $d$, the Stickelberger fractional-part multiset $\{\langle ac/d\rangle\}_c$ is the *same* for every unit $a$ (multiplication by a unit permutes $\mathbb{Z}/d$). So the valuation multiset of $g(\chi^a)$ is $a$-independent and carries no per-character phase. This is the exact, machine-checked reason the product-formula / Mahler-measure route is phase-blind: all conjugates of $g(\chi)/\sqrt p$ lie on the unit circle, so the Mahler measure is $1$ and the product formula yields *zero* phase information.

**Reduces to.** Plancherel pins the orbit RMS at $\sqrt n$ ($\sum_{b\neq0}|\eta_b|^2 = n(p-n)$, verified $= 4104$ exactly at $p=521, n=8$; coset RMS$^2 = n(p-n)/(p-1) \to n$, deficit $\Theta(n^{-3})$ at prize scale). Galois averaging recovers the magnitude floor $\sqrt n$ and *never* the max; $M/\text{RMS}$ grows as $\sqrt{\log m}$ ($2.67, 3.46, 4.06$ at $n=8,16,32$) — the extreme-value spread that lives purely in phases. Distinct Gauss sums $g(\chi_a), g(\chi_{ta})$ differ by *non-root-of-unity* phases (exact: $0.176, 0.335, -0.670,\dots$ times $2\pi$ at $p=521$), so the descent cannot self-improve. The reduction target, `GaloisPhaseSpreadResidual`: bound the orbit extreme $M$ by $C\sqrt{n\log m}$ given only the $\sqrt n$ RMS.

**Honesty — and the corrected overclaim.** The RMS hypothesis *alone* yields only $\max \le \sqrt{mn} = \sqrt p$ (all mass on one coset = the Weil bound; at $n=16$, $\sqrt{mn} = 256 = \sqrt{65537}$). Closing $\sqrt p \to \sqrt{n\log m}$ ($256 \to 11.5$, a $22\times$ gap) is the *entire* prize gap, well more than the half-power. So the residual is **not** genuinely cleaner — it is $M \le C\sqrt{n\log m}$ relabeled in orbit coordinates *plus* a magnitude constraint that every phase-blind method already saturates. The Lean `GaloisOrbitRMS := \sum v_i^2 = mn` idealizes the exact $n(p-n)/(p-1)$ to exactly $n$ — a legitimate, clearly-flagged asymptotic abstraction. *A faithful, axiom-clean obstruction proof that the descent collapses to the MRS phase-blind floor; the tool is secretly magnitude/$\ell^2$ — it only ever sees the orbit RMS. Not a closure, not a lever.*

### 3.4 The Gauss-phase transport DFT

**Construction.** Since $\eta_b$ depends only on the coset $b\mu_n$, it is a function on the cyclic quotient $\mathbb{F}_p^\times/\mu_n \cong \mathbb{Z}/m$, with the Frobenius dilation acting as a single $m$-cycle. Take the DFT of $j \mapsto \eta$ over $\mathbb{Z}/m$. *Exactly*: the spectrum is supported on all $m-1$ nontrivial frequencies, each coefficient of modulus $\sqrt p/m$ and equal to $g(\chi_r)/m$. Normalize to the **unit-modulus phase vector** $w_r = g(\chi_r)/\sqrt p \in S^1$ and form its transport-DFT $G(j) = \sum_r w_r\zeta^{rj}$. This recasts Paley as a **DFT-flatness** (Rudin–Shapiro-type) statement about the explicit Gauss phases, then *tests* the transport (bounded-variation) hypothesis on those phases.

**What it proves (axiom-clean).** `PhaseTransport.plancherel_phase_floor`: Parseval $\sum_j|G(j)|^2 = m(m-1)$ yields $\max_j|G(j)| \ge \sqrt m$ — the exponent-$1/2$ *lower* bound on the phase side. `#print axioms` clean.

**Reduces to / the corrected master identity.** The genuinely-new *negative* fact: the phase vector has **maximal total variation**, $\mathrm{TV}(w) = \sum_r|w_{r+1}-w_r| = 1.263\,m$ ($n=8$) and $1.261\,m$ ($n=16$) — indistinguishable from the random-unit value $(4/\pi)m \approx 1.27\,m$. So $w$ is *not* smooth; summation-by-parts $|G(j)| \le \mathrm{TV}/|1-\zeta^j| \approx m^2 \gg \sqrt{m\log m}$ is useless. The transport lever **fails for a precise, computed reason: there is no spectral-gap / bounded-variation structure to exploit.**

**Honesty — the headline correction.** The originally-claimed "master identity" $M = (\sqrt p/m)\max_j|G(j)|$ is *false as written*: because the spectrum is flat at $\sqrt p$, its RHS is $(\sqrt p/m)\cdot\sqrt p = p/m = n$ **identically** ($8.0019, 16.0002$), not $M$ ($7.5582, 13.8375$). The claimed "$10^{-3}$ match" was a labeling error. The genuinely-correct identity is $M = (\sqrt p/m)\max_t|\sum_j w_j\zeta^{tj}|$ — the max of the *inverse* DFT (physical/coset space), verified to $\sim 1\%$ (residual = the DC term). The reduction *direction* is real; the brick mislabeled which max equals $M$. The Plancherel brick proves only the trivial $M \ge \sqrt n$ lower bound. *The durable artifact is the negative structural theorem — the Gauss-phase vector has maximal total variation, hence every deterministic phase-smoothness/transport method must fail — the precise phase-side complement to the phase-blind-energy floor. The faithful re-encoding has zero new estimating power.*

## 4. Prove versus disprove: the refutational angles

If the conjecture is **false**, there is a sequence $p_n$ with $M/\sqrt{n\log p}\to\infty$, or a phase-anti-concentration lower bound forcing it. Two angles pursue this genuinely.

### 4.1 Anti-concentration: the disproof is refuted at every moment order

**Mechanism.** Apply Paley–Zygmund to $Z = \|\eta_b\|^2$: a disproof needs the family **heavy-tailed**, some $\rho_k = \mathbb{E}\|\eta_b\|^{2k}/((2k-1)!!\,n^k) > 1$ (super-Gaussian). The moments are *exactly computable* via (F4): $\sum_{b\neq0}\|\eta_b\|^{2k} = p E_k - n^{2k}$.

**What the computation shows.** I recomputed every quantity from scratch (Python exact integer + double precision):

- $E_2(\mu_n) = 3n^2 - 3n$ **exactly** — and **constant across all primes** $p\equiv1\pmod n$ near $n^4$, *including the Fermat prime* $F_4 = 65537$ where one would most expect phase alignment. I verified $E_2 = 168, 720, 2976$ at $n=8,16,32$, matching $3n^2-3n$ to the integer. The structured primes do **not** inflate the fourth moment.
- The limiting kurtosis is $\kappa = E_2/n^2 = 3 - 3/n$, approaching the Gaussian value $3$ strictly **from below**: $2.625, 2.8125, 2.90625$ at $n=8,16,32$ (I reverified to five digits). **Sub-Gaussian, not heavy-tailed.**
- All-order: $\rho_k < 1$ at every measured $k=1..6$, *decreasing* in $k$, obeying the exact deficit law $\rho_k(n) = 1 - \binom{k}{2}/n + o(1/n)$ (the binomial coefficient confirmed: $n(1-\rho_k) \to \{1,3,6\} = \binom{k}{2}$).

**Consequence.** With sub-Gaussian moments, Paley–Zygmund certifies only $\max\|\eta_b\|^2 \gtrsim n$, i.e. $M \gtrsim \sqrt n$ — the trivial Plancherel floor, short of $\sqrt{n\log p}$ by a full $\sqrt{\log p}$. **No finite-moment anti-concentration argument can disprove Paley.** This is the lower-bound mirror of §2: magnitude methods cannot *disprove* it above the $\sqrt n$ floor, just as they cannot *prove* it below exponent $1$. Machine-checked in `_AntiConcKurtosisRefuted.lean` (`no_kurtosis_disproof`, `#print axioms` clean — though the Lean content is the arithmetic tautology $3n^2-3n < 3n^2$ about a `def`; the math is the verified computation).

**Honesty — the scope correction.** $\rho_k$ is an *average over $b$* of magnitudes — the canonical phase-blind object, the exact dual of `_AvMRS_PhaseBlindEnergyFloor`. It refutes only the *Paley–Zygmund single-$Z$ disproof*. A genuine disproof would need **one** large $\eta_b$ from constructive phase interference — a per-$b$ alignment event *invisible* to $b$-averaged moments. So sub-Gaussianity cannot touch a *phase*-anti-concentration disproof. *The honest verdict is **refutes-the-tool**: this kills the moment-disproof route, but it is evidence against one disproof tool only, not positive evidence that Paley is true.*

### 4.2 Structured-prime counterexample search

**Mechanism.** Hunt for a divergent $C(n) = M/\sqrt{n\log(p/n)}$ at the worst structured primes (high $2$-adic valuation, Fermat). A phase-tail-temperature $c(n,p)$ — the exponential decay rate of $|\eta_b|^2/n$ in the moderate upper tail — was proposed as the carrier of the worst-case constant, with an iid random-phase surrogate to separate genuine arithmetic anti-concentration from the extreme-value-of-$N$ artifact.

**What the computation shows.** I recomputed $C$ and $C^2$ at the smallest prime $\equiv1\pmod n$ near $n^4$:

| $n$ | $p$ | $M$ | $C = M/\sqrt{n\log(p/n)}$ | $C^2$ |
|---|---|---|---|---|
| 8 | 4129 | 7.5582 | 1.0692 | 1.1432 |
| 16 | 65537 | 13.8375 | 1.1995 | 1.4388 |
| 32 | 1048609 | 22.9834 | 1.2600 | 1.5877 |
| 64 | 16777601 | 38.5286 | 1.3635 | 1.8590 |

The maximal-$2$-adic prime is *not* the worst case (at $n=128$, high-$v_2$ primes are systematically milder). The proposed moderate-tail temperature $c(n) = 1.527, 1.575, 1.606, 1.622, 1.629$ does converge geometrically (steps halving) to $c_\infty \approx 1.635$, suggesting $C_\infty \approx 1.28$, matching the constant the campaign repeatedly observes saturating near $1.28$.

**Honesty — the decisive correction.** The load-bearing identity $C(n) = \sqrt{c(n)}$ is **false**. The conjecture's actual carrier is $C^2 = (M^2/n)/\log(p/n)$, and I measure $C^2 = 1.14 \to 1.44 \to 1.59 \to 1.86$ at $n=8,16,32,64$ — **monotonically rising, not saturating**. The moderate-tail temperature $c(n)$ is a *different, tamer* interior statistic: $\sqrt{c}$ *undershoots* the real $C$ and the gap *widens* with $n$. So $c(n)$ and $C^2$ are decoupled; $c(n)$ saturating says nothing about $C^2$ drifting. The "drift" the tool labels an EVT-of-$N$ artifact is present in $C^2$ *itself*, which **is** the max the conjecture is about. The tool reads an $|\eta_b|^2$ decay rate — a magnitude/$\ell^2$ statistic — and never sums the explicit phases; it is therefore phase-blind, the exact diagnosed failure mode. *No counterexample found (correct), but the inference "saturating $c(n) \Rightarrow$ bounded $C \Rightarrow$ Paley true" is unsupported. The diagnostic gives **no evidence either way**. Verdict: no-progress, headline overclaim corrected.*

**The genuine state of the empirical evidence.** Setting aside the decoupled $c(n)$ statistic: the *directly measured* $C(n)$ rises $1.07 \to 1.36$ over $n=8..64$ and the wider campaign (40-prime windows, $n$ to $256$) finds it bounded below $\sqrt2 \approx 1.41$ with the Fermat primes worst but receding at $\beta=4$, and no prime achieving divergence. This is genuine but *bounded-window* evidence consistent with the conjecture being **true** — it cannot reach the asymptotic, and a counterexample above $n=256$ or at non-smallest structured primes is not excluded. The honest reading is: the floor is *empirically true* with $C \in [1.07, 1.41]$ and no observed drift toward $\infty$, but $C^2$ is still *rising* at accessible $n$ and has not visibly saturated — so the numerics neither prove nor disprove, and the rising $C^2$ is a caution against premature confidence in either direction.

## 5. The honest frontier

### 5.1 What was and was not achieved

**Achieved (real, keepable).** Six genuinely-new *phase-aware* objects, four of them with small axiom-clean Lean theorems (`#print axioms` $\subseteq \{$`propext`, `Classical.choice`, `Quot.sound`$\}$, no `sorryAx`). Each brings the exact Gross–Koblitz/Stickelberger/Galois phase data to bear for the first time in this campaign — every prior framework bounded $|g(\chi)| = \sqrt p$ and discarded the phase. The decisive structural facts proved: the explicit phase sum is a self-tautology (GK1, reverified to $10^{-13}$); the Hasse–Davenport coboundary is a $\sqrt p$ Jacobi sum, non-bilinear (GK2); the Stickelberger valuation multiset is character-independent, so the product-formula route is provably phase-blind (Galois `stickelberger_fracparts_const`); the Gauss-phase DFT vector has *maximal* total variation, so every transport/smoothness method must fail (PhaseTransport); the period family is sub-Gaussian at every finite moment order, $\rho_k = 1 - \binom k2/n$, so no finite-moment anti-concentration can disprove the conjecture (AntiConc, reverified).

**Not achieved.** None of the six crosses the wall. No proof, no disproof, no new lever ($\mathrm{isRealNewLever} = \texttt{false}$ for all six). Three of the four constructive reductions are *self-referential* relabelings of $M$ in phase coordinates (GK1, orbit-collapse, transport-DFT), and the fourth (Galois) reduces to a residual whose magnitude hypothesis is exactly what the phase-blind methods already saturate. Two headline claims were *corrected* during stress-testing and must be recorded as such: the transport "master identity" $M = (\sqrt p/m)\max_j|G(j)|$ is false (RHS $= n$ identically; the correct identity uses the *inverse* DFT), and the counterexample-search identity $C = \sqrt{c(n)}$ is false ($C^2$ rises while $c$ saturates). The anti-concentration result is correctly scoped only as *refutes-one-disproof-tool*, not as positive evidence for truth.

### 5.2 The single cleanest phase-statement the conjecture reduces to

Across all four constructive angles, the open core relocates to **the same** object, now stated three equivalent ways:

> **(Phase residual.)** With $w_r = g(\chi_r)/\sqrt p \in S^1$ the unit-modulus Gauss phases over $H^\perp$ (equivalently $e^{i\theta_r}$, $\theta_r = \arg\prod\Gamma_p$ the archimedean Gross–Koblitz residual), prove
> $$
> \max_t \Big|\sum_{r} w_r\,\zeta^{rt}\Big| \;\le\; C\sqrt{m\log m}, \qquad \zeta = e^{2\pi i/m}.
> $$

This is a *flatness* statement about the DFT of an explicit, unit-modulus, maximal-total-variation $S^1$-valued sequence. It is the BGK wall stated entirely in the phases. The three faces: GK1 says summing the explicit phases returns this character sum; the orbit-collapse says the phases align constructively at $b^\star$; the Galois descent says the only provable constraint is the $\sqrt n$ RMS (= the Parseval floor $\max \ge \sqrt m$, formalized). The Stickelberger result certifies that this archimedean residual is *untouched* by all $\pi$-adic/valuation data — it is genuinely the part the magnitude methods never see.

**Is it more tractable than $M$?** Honestly: *no, not yet*. By GK1 the target **is** $\eta_b$ in phase coordinates — a faithful relabeling, not a more-tractable object. The maximal total variation (PhaseTransport) shows the sequence has no exploitable deterministic regularity (no spectral gap, no bounded variation). What the reduction *does* deliver is a **clean, exact, phase-only target**: the open problem is now a single concrete flatness inequality about one explicit $S^1$-valued sequence, with the magnitude/valuation data certified irrelevant. That is a map, not a key.

### 5.3 What genuinely-new mathematics would be needed

The phase residual is a Rudin–Shapiro-type flatness statement for the Gross–Koblitz archimedean phases. Closing it requires something *none* of the fifty-plus frameworks supplies: a handle on $\arg\prod\Gamma_p$ over the arithmetic progression $a = nj$ that is **not** a magnitude, **not** a valuation, and **not** a bilinear/quadratic linearization (GK2 rules out the obvious one — $\arg J$ is itself a $\sqrt p$ Jacobi sum). Candidate directions, all genuinely open: (i) an equidistribution-with-cancellation theorem for the $p$-adic Gamma phases that beats the random-phase ceiling on the *specific* progression $nj$ — a growing-rank big-monodromy input, which prior campaign work found necessary and unavailable; (ii) a Weingarten/Jacobi self-map identity that linearizes the cochain $\arg J$ enough to extract $\sqrt m$ (currently refuted at the naive level by GK2's non-bilinearity, but not impossible in a higher structure); (iii) a phase-anti-concentration *lower* bound — the disproof side — which §4.1 shows must evade all $b$-averaged moments and live in a per-$b$ alignment event, an object no current tool reaches.

The empirical picture is consistent with the conjecture being **true** (worst-case $C$ bounded below $\sqrt 2$, no observed divergence to $n=256$, Fermat primes worst but receding at $\beta=4$), with the one honest caution that $C^2$ is still *rising* at accessible $n$ and has not visibly saturated. The diagnosis is firm: the half-power gap is pure phase cancellation, the explicit phases are provable only on their magnitude shadow, and the wall is now mapped — for the first time — in the phases rather than the magnitudes. **If nothing crosses, the sharpest honest reduction is the phase residual of §5.2: an exact, phase-only flatness inequality for the maximal-total-variation Gross–Koblitz phase vector, with the valuation data certified irrelevant. That cleaner phase-side map of the wall, plus the four small machine-checked theorems pinning *why* the explicit phase formula is phase-blind in its provable part, is the real and honest contribution.**

---

### Files (axiom-clean, `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}, no sorryAx)

- `Research/ProximityPrize/Frontier/_AvMRS_PhaseBlindEnergyFloor.lean` — the floor theorem (§2.1)
- `Research/ProximityPrize/Frontier/_AvGK_GrossKoblitzPhaseCochain.lean` — GK1/GK2/GK3 (§3.1)
- `Research/ProximityPrize/Frontier/_PhaseCorrelationOrbitCollapse.lean` — orbit-collapse identity (§3.2)
- `Research/ProximityPrize/Frontier/_AvGalois_StickelbergerPhaseDescent.lean` — Galois RMS descent + Stickelberger character-constancy (§3.3)
- `Research/ProximityPrize/Frontier/_AntiConcKurtosisRefuted.lean` — sub-Gaussian-at-every-order (§4.1)

Verification scripts (reproduced for this essay): GK1 tautology $|\Sigma/m-\eta| = 2.9\times10^{-14}$; $E_2 = 3n^2-3n$ and $\kappa = 3-3/n$ exact; orbit-rep multiplicity $\sum r(d_0) = n-1$ exact; $C^2 = 1.14, 1.44, 1.59, 1.86$ rising at $n=8,16,32,64$.