# Analytic CORE Orbit-Class Laws, Odd-Depth Subset-Sum Freeness, and 32-Colour Joint Period Rigidity

**Module:** `ArkLib/Research/ProximityGap/Frontier/CarbonBGKCoreOrbitAndPeriodLaws.lean`  
**Probe / Style Audit:** `scripts/probes/probe_carbon_bgk_core_orbit_period.py`  
**Honesty Status:** Unconditional structural theorems + kernel-certified production prime invariants (zero `sorry`, zero new `axiom`; standard `{propext, Classical.choice, Quot.sound}` only; analytic BGK / depth-7 `126871` variance target remains open).

---

## 1. Summary of Results

This note and companion Lean 4 module advance the **Analytic CORE** behind both Proximity Prize Grand Challenges across three tightly linked axes, built purely on prebuilt canonical substrate modules (`SubgroupGaussSumSecondMoment`, `SubgroupGaussSumMoment`, `DCSubtractedMoment`, `DCEnergyCorrection`, `GaussPeriodCosetReduction`, `_PrizeShapePrimeP30`, `_PrizeShapePrimeP30Second`):

1. **Odd-Cardinality Subset-Sum Stabilizer-Freeness (`n \mid a_0`) and Orbit-Class Parseval Laws (`§1`):**
   - For even subset sizes $r = 2k$ (e.g. $r = 2, 6$), multiplication by $-1 \in \mu_{2^m}$ can stabilize antipodal zero-sum subsets, so $|G|$ does *not* divide the zero-sum subset count $a_0(G, 2k)$.
   - **`odd_subset_stabilizer_eq_one` & `card_dvd_zero_subsetSumCount_of_odd`**: For **every odd subset cardinality $r$** (specifically the depth-7 injective residual $r = 7$ of `BGKDepthSevenInjectiveVarianceEquivalence`) over any dyadic root subgroup $G = \mu_{2^m}$ in odd characteristic:
     - Multiplication by $c \in \mu_{2^m}$ stabilizing any odd-cardinality subset $S \subseteq G$ forces $c^{|S|} = 1$ (by cancelling $\prod_{x \in S} x \ne 0$ from $\prod_{x \in S} (c x) = \prod_{x \in S} x$), which together with $c^{2^m} = 1$ and $(-1)^{|S|} = -1 \ne 1$ forces **$c = 1$ unconditionally**—even without antipode-freeness!
     - Consequently, $G$ acts **freely** on the zero-sum $r$-subset fiber $\{S \in \binom{G}{r} : \sum_{x \in S} x = 0\}$, proving **exact subgroup divisibility $|G| \mid a_0(G, r)$** ($a_0(G, 7) = n\,z_0$ at $n = 2^{30}$).
   - **`subsetSum_nonzero_parseval`, `subsetSumCount_mul_mem`, & `subsetSum_nonzero_parseval_ge_zero_and_mean`**: Proves the exact subset-sum Parseval identity
     $$\sum_{b \ne 0} \left\|\sum_{S \in \binom{G}{r}} \psi\!\left(b \sum_{x \in S} x\right)\right\|^2 = |F| \sum_{y \in F} a_y(G, r)^2 - \binom{n}{r}^2,$$
     invariance $a_{c y}(G, r) = a_y(G, r)$ along $G$-cosets, and the two-term lower bound isolating the zero-sum necklace count $z_0 = a_0 / n$ from the uniform nonzero-fiber baseline:
     $$|F|\,a_0^2 + \frac{|F|\,(\binom{n}{r} - a_0)^2}{|F| - 1} - \binom{n}{r}^2 \le \sum_{b \ne 0} \left\|\sum_{S \in \binom{G}{r}} \psi\!\left(b \sum_{x \in S} x\right)\right\|^2.$$
     At $r = 7$ (`D_7(b) = 7! · subsetFourier ψ G 7 b`), this directly brackets the zero-sum 7-necklace count $z_0$ under the depth-7 `126871` variance target.

2. **Kernel-Certified 32-Colour Cyclotomic Separation, $32 \times 32$ Regular-Simplex Gram Matrix, 992-Fraction Rational Exclusion, and 32-Step Harmonic Ladder (`§2`):**
   - **`firstPrime_smallCoset_injOn` & `secondPrime_smallCoset_injOn`**: Extends the 7-colour cyclotomic check (`1..7`) by $4.5\times$ to **`1..32`** at **both** designated primes $P_1$ and $P_2$ using fast 30-step modular repeated squaring (`natSquareTower`) and `List.inj_on_of_nodup_map`, requiring only $33$ modular exponentiations per prime in the Lean kernel.
   - **`firstPrime_small_rational_not_in_roots` & `secondPrime_small_rational_not_in_roots`**: Deduces unconditionally in the kernel that **all $32 \times 31 = 992$ nontrivial signed small rationals $\pm a / b$ ($1 \le a \ne b \le 32$)** avoid $\mu_{2^{30}}(\mathbb{F}_{P_1})$ and $\mu_{2^{30}}(\mathbb{F}_{P_2})$:
     $$\left(\pm \frac{a}{b}\right)^{2^{30}} \ne 1 \pmod{P_i} \qquad (1 \le a \ne b \le 32,\ i \in \{1, 2\}).$$
     In particular, $(3 : \mathbb{F}_{P_i})^{2^{30}} \ne 1$ holds unconditionally in the kernel at both primes (discharging the `(3 : F)^n ≠ 1` side condition of `SixthMomentSignatureBridge`), and every small integer $\pm 2, \pm 3, \dots, \pm 32$ lies outside $\mu_{2^{30}}$.
   - **`distinct_cosets_gram_entry`**: Proves that whenever $r^n \ne s^n$, the dilated cosets $r G$ and $s G$ are disjoint, forcing exact full-frequency orthogonality $\sum_b \eta_{r b}\overline{\eta_{s b}} = 0$ and DC-subtracted negative correlation $\sum_{b \ne 0} \eta_{r b}\overline{\eta_{s b}} = -n^2$, establishing the **exact $32 \times 32$ regular-simplex off-diagonal Gram law** (`diag = P_i n - n^2`, `off-diag = -n^2`) across the $32$ certified cosets at both $P_1$ and $P_2$.
   - **`distinct_cosets_ladder_sq_le` & `firstPrime_32_ladder_sq_le` / `secondPrime_32_ladder_sq_le`**: Discharges the distinct-coset arithmetic side condition up to $H = 32$ at both $P_1$ and $P_2$, proving uniformly for every dilation $b \ne 0$:
     $$\sum_{h=0}^{31} \left\|\eta_{(h+1)b}\right\|^2 \le P_i - 2^{30}$$
     (an exact $2^{30}$-fold coset-degeneracy reduction over the frequency-level Parseval bound $P_i \cdot 2^{30} - 2^{60}$).

3. **$n$-Fold Tightened Coset-Reduced `DCEnergyBound` Per-Frequency Sup-Norm (`§3`):**
   - **`eta_pow_le_of_dcEnergyBound_cosetReduced`**: `DCEnergyCorrection.eta_pow_le_of_dcEnergyBound` bounded $\|\eta_b\|^{2r} \le |F|\,(2r-1)!!\,|G|^r$ via single-frequency domination, losing the $|G|$-fold coset multiplicity of $\|\eta_b\|$. Combining `DCEnergyBound G r` with `GaussPeriodCosetReduction.cosetReduced_eta_pow_le` proves
     $$|G| \cdot \|\eta_b\|^{2r} \le |F|\,(2r - 1)!!\,|G|^r \qquad (\forall b \ne 0),$$
     or equivalently $\|\eta_b\|^{2r} \le |F|\,(2r - 1)!!\,|G|^{r - 1}$ when $G$ is nonempty—the exact $n$-fold tightening needed so that tuning $r \asymp \log(|F|/|G|)$ eliminates the spurious $n^{1/(2r)}$ factor and matches the $\sqrt{n \log(|F|/n)}$ scale.
