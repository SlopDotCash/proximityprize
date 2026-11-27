# Degree-2 Confluent Shift-Stepanov Bounds, Unconditional $O(n^{2r - 4/3})$ Moment Ladder, Sum-Product Expansion, and Midpoint-Resonance Exclusion

**Module:** `ArkLib/Research/ProximityGap/Frontier/CarbonBGKM4ConfluentStepanovAndMoments.lean`  
**Probe / Style Audit:** `scripts/probes/probe_carbon_bgk_m4_stepanov_moments.py`  
**Honesty Status:** Unconditional component + kernel-certified production moment, sum-product, sextuple, and midpoint-resonance bounds (zero `sorry`, zero new `axiom`; standard `{propext, Classical.choice, Quot.sound}` only; full $\sqrt{n \log(p/n)}$ BGK cancellation and depth-7 `126871` Wick variance remain open).

---

## 1. Summary of Breakthroughs

This note and companion Lean 4 module establish four unconditional analytic and combinatorial pillars for smooth multiplicative subgroups $G = \mu_n \subset \mathbb{F}_p^\times$ ($n = 2^{30}$), built exclusively on prebuilt canonical substrate modules ([MobiusStepanov.lean](../../../ArkLib/Research/ProximityGap/Frontier/MobiusStepanov.lean), [StepanovGeneratorIndep.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/StepanovGeneratorIndep.lean), [SubgroupGaussSumFourthMoment.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupGaussSumFourthMoment.lean), [CharPDeepMomentTail.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CharPDeepMomentTail.lean), [DCEnergyCorrection.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/DCEnergyCorrection.lean), [_PrizeShapePrimeP30.lean](../../../ArkLib/Research/ProximityGap/Frontier/_PrizeShapePrimeP30.lean), and [_PrizeShapePrimeP30Second.lean](../../../ArkLib/Research/ProximityGap/Frontier/_PrizeShapePrimeP30Second.lean)):

### 1.1 Degree-2 Confluent Graded Shift-Stepanov Engine (`§1`)

In [MobiusSubgroupBound.lean](../../../ArkLib/Research/ProximityGap/Frontier/MobiusSubgroupBound.lean), affine shifts $a x + b = y$ on $\mu_n$ were reduced via $x \mapsto x^{-1}$ to fractional-linear maps with a finite pole, forcing the auxiliary polynomial through the **degree-3** clearing multiplier $X(X - a)(X - b)$ whose $r$-th cleared derivative has residual degree $\le 2r$ and graded condition count $D(A + D - 1)$, giving the production cap $3{,}143{,}679 \approx 2.998\,n^{2/3}$.

For pure additive coset shifts $x^N = c_0 \wedge (x - a)^M \in \{K_0, \dots, K_{J-1}\}$ (`shiftTerm a e i = X^e (X - a)^i`), there is **no finite pole**:

- **`shiftAux_ne_zero` & `deg_shiftResidual`**: Clearing by the **degree-2** polynomial `shiftClearing a = X (X - a)` produces a **degree-1** logarithmic derivative factor `shiftLogFactor a e i = e(X - a) + i X`, so the $r$-th cleared derivative residual satisfies $\deg(\mathrm{shiftResidual}_r) \le r$ (cutting the derivative degree penalty in half).
- **`shift_stepanov_count_many_graded` & `coset_shift_rectangular_many`**: Halving the derivative degree growth reduces the triangular graded condition space `GradedShiftCoeffs A D` from $D A + D(D - 1)$ to $D A + D(D - 1)/2$, lowering the asymptotic Stepanov / Garcia–Voloch leading constant from $3$ to $3 / 2^{1/3} \approx 2.3811$ at the asymmetric optimum $(A, C, B, D) \asymp (2^{-1/3} n^{2/3},\, 2^{1/3} n^{1/3},\, 2^{4/3} n^{1/3},\, 2^{2/3} n^{2/3})$, uniformly across arbitrary source cosets $x^N = c_0$.
- **`production_coset_shift_count` & `production_fourCoset_shift_count`**: At $N = M = 2^{30}$ for every prime $p > 2^{41}$ (including both certified production primes $P_1, P_2$), setting $(A, C, B, D) = (838{,}860,\, 1{,}280,\, 2{,}490,\, 1{,}621{,}001)$ proves unconditionally:
  $$\#\bigl\{x \in \mathbb{F} : x^{2^{30}} = c_0 \wedge (x - a)^{2^{30}} = K\bigr\} \le 2{,}495{,}902 < 2^{22} \qquad (a, c_0, K \ne 0),$$
  improving `MobiusSubgroupBound.production_graph_graded` ($3{,}143{,}679$) by $647{,}777$ points ($20.6\%$), while $(A, C, B, D) = (542{,}293,\, 1{,}980,\, 4{,}060,\, 1{,}030{,}530)$ bounds simultaneous shifts into **any $4$ target cosets** (e.g. an entire $\mu_{2^{32}}$-coset) by $6{,}291{,}183 < 6\,n^{2/3}$.

---

### 1.2 Exact Difference-Autocorrelation Moment Step, Unconditional $O(n^{2r - 4/3})$ Moment Ladder, and Cross-Coset Sextuple Bounds (`§2`)

- **`rEnergy_succ_eq_diffCount_autocorr` & `sum_erase_zero_autocorr_eq`**: Grouping `CharPMomentRecursion.rEnergy_succ_double_sum` by $\delta = s - t$ yields the exact identity valid for *every* finite subset $G \subseteq \mathbb{F}$:
  $$E_{r+1}(G) = |G|\,E_r(G) + \sum_{\delta \ne 0} \mathrm{diffCount}(G, \delta)\,\mathrm{autocorr}_r(G, \delta), \qquad \sum_{\delta \ne 0} \mathrm{autocorr}_r(G, \delta) = |G|^{2r} - E_r(G).$$
- **`rEnergy_succ_le_of_diffBound` & `rEnergy_le_mul_pow_of_diffBound`**: Whenever $\mathrm{diffCount}(G, \delta) \le M$ for all $\delta \ne 0$ and $M + 1 \le |G|$, induction from $E_1(G) = |G|$ closes cleanly at **every rung $r \ge 2$**:
  $$E_r(G) \le (M + 1)\,|G|^{2r - 2},$$
  saving a full factor of $|G|/(M + 1)$ over `CharPDeepMomentTail.rEnergy_le_pow_sharp` ($|G|^{2r - 1}$) at every moment order simultaneously.
- **`production_gvRepBound_unconditional` & `production_moment_ladder_unconditional`**: Discharges the Garcia–Voloch / HBK condition $\mathrm{repCount}(G, t) = \mathrm{diffCount}(G, t) \le 2{,}495{,}902$ with $2{,}495{,}902^3 \le 64\,|G|^2$ unconditionally on $G = \mu_{2^{30}}$ ($p > 2^{41}$), yielding for all $r \ge 2$:
  $$E_r(\mu_{2^{30}}) \le 2{,}495{,}903 \cdot 2^{30(2r - 2)}, \qquad \sum_{b \in \mathbb{F}} \|\eta_b\|^{2r} \le |\mathbb{F}| \cdot 2{,}495{,}903 \cdot 2^{30(2r - 2)}$$
  (a $430\times$ improvement over $2^{30(2r - 1)}$ across the fourth, sixth, eighth, and fourteenth Gauss-sum moments, and $215\times$ sharper than [StepanovUnconditionalEnergy.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/StepanovUnconditionalEnergy.lean) at $r = 2$).
- **`nonAntipodalCrossSextuples_card_le` & `production_crossCoset_sextuples_le`**: Extends cross-coset zero-sum sextuple control beyond $\mu_4$ to **arbitrary sub-cosets $C_1, C_2, C_3 \subseteq \mu_{2^{30}}$** (including $\mu_8, \mu_{16}, \dots, \mu_{2^{30}}$), bounding ordered zero-sum sextuples $(x_1, x_2, y_1, y_2, z_1, z_2) \in C_1^2 \times C_2^2 \times C_3^2$ with $z_1 + z_2 \ne 0$ by $\min(|C_3|, 2{,}495{,}902) \cdot |C_1|^2 |C_2|^2$.

---

### 1.3 Quantitative Sum-Product Expansion ($|G + G| > 430\,|G|$), `DCEnergyBound` Sumset Growth, and Real-Spectrum Law (`§3`)

- **`sumset_card_mul_rEnergy_ge` & `production_sumset_expansion_unconditional`**: Cauchy–Schwarz on `freq G r` over `rFoldSumset G r` gives $|G|^{2r} \le |\Sigma^r G|\,E_r(G)$. Specializing to $r = 2$ on $G = \mu_{2^{30}}$ ($p > 2^{41}$) proves unconditionally:
  $$|G \cdot G| = 2^{30} \qquad \text{while} \qquad |G + G| \ge 461{,}925{,}605{,}526 > 430\,|G| \quad (\ge 0.40\,|G|^{4/3}).$$
- **`sumset_card_ge_of_dcEnergyBound`**: Under `DCEnergyBound G r`, whenever $|G|^r \le c\,|\mathbb{F}|$, $((2r - 1)!! + c)\,|\Sigma^r G| \ge |G|^r$ (e.g. $c = 1$ at $P_1, P_2$ for $r \in \{2, 3, 4, 5\}$).
- **`eta_eq_star_and_im_zero_of_neg_closed`**: For any $-1$-closed subset $G = -G$ (all even-order subgroups $\mu_{2k}$), $\overline{\eta_b} = \eta_b$ and $\operatorname{Im}(\eta_b) = 0$ for every frequency $b \in \mathbb{F}$.

---

### 1.4 Unconditional Midpoint-Resonance Cap and Exclusion of $1 \to 2$ Wick Defect at $P_1, P_2$ (`§4`)

- **`rEnergy_two_ge_three_card_sq_sub`, `firstPrime_midpoint_and_no_firstStep_defect`, & `secondPrime_midpoint_and_no_firstStep_defect`**: Proves unconditionally on $G = \mu_{2^{30}}(\mathbb{F}_{P_i})$ ($i \in \{1, 2\}$) that $|G| = 2^{30}$, $E_2(G) \ge 3 \cdot 2^{60} - 3 \cdot 2^{30}$, and
  $$\mathrm{midpointCount}(G) = \#\{(x, y, z) \in G^3 : x + y = 2z\} \le 2{,}495{,}902 \cdot 2^{30} < 2^{52} \ll 2^{59},$$
  eliminating the unproved `hrep` hypothesis of [_BGKActualJointPeriodLaw.lean](../../../ArkLib/Research/ProximityGap/Frontier/_BGKActualJointPeriodLaw.lean) and proving unconditionally that the $1 \to 2$ Newton transition cannot supply a one-unit Wick defect at either designated prime.
