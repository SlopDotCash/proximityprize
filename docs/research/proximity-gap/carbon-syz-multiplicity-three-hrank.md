# Multiplicity-3 Twisted-Syzygy Confinement and Determinantal Union-Rank (`hrank`) Without Overlap Chaining

## Summary and Honesty Classification (`DOSSIER.md` §6)

This note documents the machine-checked results in
[`CarbonSYZMultiplicityThreeHrank.lean`](../../../ArkLib/Research/ProximityGap/Frontier/CarbonSYZMultiplicityThreeHrank.lean)
and companion verification script
[`probe_carbon_syz_mult3_hrank.py`](../../../scripts/probes/probe_carbon_syz_mult3_hrank.py).

Per `DOSSIER.md` §6, the theorems in `CarbonSYZMultiplicityThreeHrank.lean` are **unconditional
structural components and exact boundary characterizations** for the F3 union-rank obligation
(`hrank` in `SYZ43.realizabilityCore_of_overBudget_stack`, `DOSSIER.md` §3.2 F3):

1. **Multiplicity-3 Support Confinement of Twisted G87 Syzygies (`twisted_syzygy_confined_to_multThree`).**
   For any witness-support family $\{S_i\}_{i < r} \subseteq \iota$, any injective scalar tuple
   $\gamma : \mathrm{Fin}\, r \to F$, and any linear functionals $L_i \in (F^\iota)^*$ anchored on
   $S_i$, the G87 twisted syzygy equations
   $$\sum_{i=0}^{r-1} L_i = 0, \qquad \sum_{i=0}^{r-1} \gamma_i L_i = 0$$
   confine **every** $L_a$ strictly to the multiplicity-$\ge 3$ locus
   $$\mathcal{M}_3(S) := \bigl\{\, x \in \iota : \#\{i < r : x \in S_i\} \ge 3 \,\bigr\}.$$
   Any coordinate $x$ of multiplicity $1$ or $2$ is eliminated by subtracting the second witness's
   $\gamma_b$-multiple: $(\gamma_a - \gamma_b) L_a(e_x) = 0 \implies L_a(e_x) = 0$.
2. **Vandermonde / Lagrange Leaf Elimination and Iterated Peeling (`rs_twisted_syzygy_leaf_zero`,
   `peeled_bridge_linearIndependent`).**
   For any Reed–Solomon code $\mathrm{RS}[\alpha, k]$ on an injective domain $\alpha : \iota \hookrightarrow F$
   (including $\mu_{2^m}$), if $|S_a \cap \mathcal{M}_3(S)| \le k$, Lagrange interpolation
   (`ArkLib.CS25.evalOnS_surjective`) extends any values on $S_a \cap \mathcal{M}_3(S)$ to a
   codeword $c \in \mathrm{RS}[\alpha, k]$, forcing $L_a = 0$. Iterating leaf elimination across
   any `PeeledSupportFamily k S` proves **full linear independence** of the $r$-witness G87 bridge
   functionals ($\dim \mathrm{span}(\mathrm{range}\,\varphi) = \sum_i (|S_i| - k)$) **without
   overlap chaining** — working even when **all** pairwise overlaps satisfy $|S_i \cap S_j| < k$
   (the exact strip regime where `SYZ56` cross-witness chaining is a no-go).
3. **Unconditional 3-Witness Full Rank and $n = 2^{30}$ Determinantal `hrank` Realizations.**
   - **Every 3-witness family with $|S_0 \cap S_1 \cap S_2| \le k$ is `LinearIndependent`**
     (`three_witness_bridge_linearIndependent`): for $r = 3$, $\mathcal{M}_3(S) = S_0 \cap S_1 \cap S_2$,
     so single-copy polynomial syzygies ($\delta_1 = d$ or $\delta_1 = 7$) completely disappear
     under the distinct-scalar $\gamma$-twist whenever $t \le k$.
   - **Peeled tight covers realize exact `hrank` (`hrank_of_peeled_tight_cover`,
     `realizabilityCore_of_peeled_tight_cover`):** Whenever a `PeeledSupportFamily k S` satisfies
     $\sum_i (|S_i| - k) = 2(|U| - k)$ ($U = \bigcup_i S_i$), the G87 bridge functionals achieve
     $\dim_F \mathrm{span}(\mathrm{range}\,\varphi) = 2(|U| - k)$, discharging `SYZ43`'s `hrank`
     hypothesis unconditionally and forcing $|U| \le n - 1$ on any non-codeword stack.
   - **Production $n = 2^{30}$ instantiations (`production_k4Tight_hrank` and
     `production_subKOverlap_linearIndependent`):** At the exact production strip parameters
     $n = 2^{30}, k = 2^{29}, t = 715{,}827{,}884$:
     1. The $K_4$ 2-regular hypergraph cover ($e = 59{,}652{,}324$, $|U| = 894{,}784{,}856 < 2^{30}$)
        satisfies $|\mathcal{M}_3(S)| = 2^{29} \le k$ and realizes **exact `hrank`**
        $\dim_F \mathrm{span}(\mathrm{range}\,\varphi) = 2(|U| - k) = 715{,}827{,}888$ over every
        injective $2^{30}$-point domain (including both certified prize primes).
     2. The symmetric $K_4$-complement family ($p = 119{,}304{,}646, q = 2$) has $|S_i| = 715{,}827{,}884$,
        **every pairwise overlap $|S_i \cap S_j| = 477{,}218{,}590 < 2^{29} = k`** (so `SYZ56`
        overlap chaining fails on every pair), and $|\mathcal{M}_3(S)| = 357{,}913{,}948 < k$,
        certifying full G87 rank $715{,}827{,}888$ without chaining.
4. **Full-Domain Rank-Deficiency Boundary (`plantable_cannot_realize_full_domain_hrank`).**
   Conversely, for any non-codeword stack $(u_0, u_1)$, if a witness family's union covers the full
   domain ($|U| = n$, as in `FirstPrimeSepticCores` on `ZMod PrizeShapePrimeP30.P`),
   `SYZ20JointRankSuperadditive.plantable_span_cap` caps
   $\dim_F \mathrm{span}(\mathrm{range}\,\varphi) \le 2(n - k) - 1 < 2(|U| - k)$, proving that
   universal `hrank` on $U = \bigcup_i S_i$ cannot hold across arbitrary over-budget stacks when
   $|U| = n$.

## Why Multiplicity-3 Confinement Bypasses `SYZ56` Overlap Chaining

`SYZ56` attempted to merge witness cores pairwise via $|S_i \cap S_j| \ge k$, which fails inside
$(1 - \sqrt{1/2}, 1/3)$ because two sets of size $t \approx \frac{2}{3}n$ can overlap in only
$2t - n \approx \frac{1}{3}n < \frac{1}{2}n = k$ coordinates. Multiplicity-3 confinement works in
the **opposite** direction:

- Coordinates appearing in only $1$ or $2$ supports are **automatically zeroed** in any twisted
  syzygy by the $2 \times 2$ Vandermonde minor $\det \begin{pmatrix} 1 & 1 \\ \gamma_a & \gamma_b \end{pmatrix} = \gamma_b - \gamma_a \ne 0$.
- Only coordinates of multiplicity $\ge 3$ can support a nontrivial G87 syzygy, and Vandermonde
  interpolation on $\mathrm{RS}[\alpha, k]$ kills any leaf witness $S_a$ with
  $|S_a \cap \mathcal{M}_3(S)| \le k$.
