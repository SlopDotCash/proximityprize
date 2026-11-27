# Complete dihedral covariance obstructions at 671,088,640 errors

At length $n = 2^{30} = 1{,}073{,}741{,}824$, dimension $k = 2^{27} = 134{,}217{,}728$, degree $d = k - 1 = 134{,}217{,}727$, and error count $e = 5k = 671{,}088{,}640$, any overrun on the second designated prime requires four noncollinear rich heads with sorted fresh-site deficits $(1, 1, 1, q)$, $1 \le q \le 5$, and core-incidence slack $0 \le s \le q - 1 \le 4$.

Earlier work ([`eighth-dyadic-head-directions.md`](eighth-dyadic-head-directions.md), [`EighthDyadicHeadDirections.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthDyadicHeadDirections.lean)) classified rotational covariance $X \mapsto \zeta X$ on $H = \mu_{2^{30}}$, ruling out scalar antipodes and nonscalar quarter turns and pinning any nonscalar antipode to $r = 0, s = 4$.

This note and its Lean companion [`EighthDihedralHeadDirections.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthDihedralHeadDirections.lean) complete the classification across the **entire dihedral group $D_{2n} = \langle X \mapsto \zeta X,\, X \mapsto c / X \rangle$ of order $2^{31}$**, and further narrow the surviving $s = 4$ nonscalar antipode:

1. **Zero scalar reflection symmetries (all $0 \le s \le 4$)**: for *every* $c \in H$ (even or odd), using $M(x) + W(x) \le 4$ on each fixed point ($\pm a$ when $c = a^2$, so `fixedLabels + fixedCore ≤ 8`), scalar reflection covariance $z_i(c / X) = z_i(X)$ caps total fresh head labels at **$1{,}879{,}048{,}352$** ($+ 20{,}607{,}410 \ll 2n$).
2. **Universal fixed-point determinant divisibility (any field, $\operatorname{char} F \ne 2$)**: for any $a \in F^\times$ with $a^2 = c$ and any nonscalar reflection eigenbasis $\operatorname{rev}_N(c, U_i) = \varepsilon U_i$, $\operatorname{rev}_N(c, V_i) = -\varepsilon V_i$ ($\varepsilon = \pm a^N$), every $2 \times 2$ triangle determinant $U_1 V_2 - U_2 V_1$ vanishes at **both $a$ and $-a$**, hence is divisible by $X^2 - c$ regardless of the parity of $N$.
3. **Nonscalar odd reflections ($c \in H \setminus H^2$, $\pm a \notin H$)**: the factor $X^2 - c$ consumes $2$ roots *outside* $H$ in each of the four triangle determinants, proving:
   - **All four profiles $(1,1,1,1), (1,1,1,2), (1,1,1,3), (1,1,1,4)$ ($0 \le s \le 3$) are impossible.**
   - **Every even quotient degree $N$ is impossible across all $0 \le s \le 4$.**
   - At $s = 4$ ($q = 5$), the sole surviving case forces $r = 0$, $N = d$ (odd), $x_0 = x_3 = x_4 = 0$, and $x_2 = 4d - 4$ (exact saturation on the degree-$2^{26}-1$ trace quotient $\{x + c/x : x \in H\}$).
4. **Nonscalar even reflections ($c = a^2 \in H^2$, $\pm a \in H$)**: every fixed point $x \in \{a, -a\} \setminus Z(h)$ adds at least $1$ excess triangle root ($+2$ unless $W(x) = 3$ is a triple site), forcing $2r + f + \text{extra} + 8(d - r - N) \le 2s$:
   - **Exact saturation $s = 0$ ($(1,1,1,1)$) is impossible.**
   - **$r = 0$ with even $N$ is impossible across all $0 \le s \le 4$.**
   - **$r = 0, s = 1$ ($(1,1,1,2)$) forces both $a$ and $-a$ to be triple sites ($W(a) = W(-a) = 3$).**
5. **Complete dihedral triviality of saturated $(1,1,1,1)$ quartets**: combining rotations and reflections, a saturated $(1,1,1,1)$ four-head overrun at $671{,}088{,}640$ admits **zero nontrivial symmetries in $D_{2n}$** ($\operatorname{Aut}_{D_{2n}} = \{\mathrm{id}\}$).
6. **Nonscalar antipode involution exclusion ($J' \ne -\mathrm{id}$)**: in the surviving $s = 4$ nonscalar antipode $W_i(X) - W_0(X) = (A_i'(X^2), X B_i'(X^2))$, the quotient quartet on $H^2$ is exact-saturated with $4 d' = 268{,}435{,}452$ double sites ([`EighthNearSaturatedPowers.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthNearSaturatedPowers.lean)). If its constant opposite-direction involution were $J'(w) = -w$, then at every double site $y = x^2 \in H^2$ opposite fresh labels would collide pairwise across $x$ and $-x$ ($S_k(y)/x = -S_\ell(y)/x = S_\ell(y)/(-x)$), losing at least $4 d' = 268{,}435{,}452$ labels and capping the full total at **$1{,}899{,}655{,}610 \ll 2n$** (even with the baseline $20{,}607{,}410$ residual allowance).

## Summary across $D_{2n}$ at $e = 671{,}088{,}640$

| Symmetry class in $D_{2n}$ | $s = 0$ `(1,1,1,1)` | $s \in \{1,2,3\}$ `(1,1,1,2..4)` | $s = 4$ `(1,1,1,5)` |
|---|---|---|---|
| Scalar rotation $X \mapsto \zeta X$ | Impossible | Impossible | Impossible |
| Nonscalar rotation $\operatorname{ord}(\zeta) \ge 4$ | Impossible | Impossible | Impossible |
| Nonscalar antipode $X \mapsto -X$ | Impossible | Impossible | Pinned: $r=0, x_0=x_3=x_4=0$, exact $H^2$ sat., $J' \ne -\mathrm{id}$ |
| Scalar reflection $X \mapsto c/X$ (any $c \in H$) | Impossible | Impossible | Impossible |
| Nonscalar odd reflection $c \in H \setminus H^2$ | Impossible | Impossible | Pinned: $r=0, N=d, x_0=x_3=x_4=0$, exact trace sat. |
| Nonscalar even reflection $c = a^2 \in H^2$ | Impossible | $2r + f + \text{extra} + 8(d-r-N) \le 2s$ | $2r + f + \text{extra} + 8(d-r-N) \le 8$ |

## Verification ledger

- **Lean-checked (axiom-clean, zero `sorry`)**: [`ArkLib/Research/ProximityGap/Frontier/EighthDihedralHeadDirections.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthDihedralHeadDirections.lean) — all 14 public theorems verified with `#print axioms` $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$.
- **Reproducible probe**: [`scripts/probes/probe_eighth_dihedral_head_directions.py`](../../../scripts/probes/probe_eighth_dihedral_head_directions.py) numerically tests `revPoly` determinant divisibility by $X^2 - c$ across both parities of $N$ over prime fields, exhausts all $16$ fixed-point $4$-bit agreement vectors, and verifies every scalar/nonscalar reflection and antipode-involution bound.
- **Written-only geometric bridges**: reducing projective covariance $z_i(c/X) = \tau(z_i(X))$ to a reflection-covariant primitive eigenbasis $(U_i/h, V_i/h)$ via `EighthDyadicHeadDirections.{triangle_scale, primitive_scale}` and descending the nonscalar antipode opposite-direction relation to $H^2$.
