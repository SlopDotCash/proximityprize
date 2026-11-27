# Near-saturated four-head power-slope obstructions at 671,088,640 errors

At length $n = 2^{30} = 1{,}073{,}741{,}824$, dimension $k = 2^{27} = 134{,}217{,}728$, degree $d = k - 1 = 134{,}217{,}727$, and error count $e = 5k = 671{,}088{,}640$, any overrun on the second designated prime requires four rich heads (no three collinear) with sorted fresh-site deficits $(1, 1, 1, q)$, $1 \le q \le 5$, and core-incidence slack $0 \le s \le q - 1 \le 4$.

Previously ([`saturated-power-translations.md`](saturated-power-translations.md), [`PowerSlopeCoincidences.lean`](../../../ArkLib/Research/ProximityGap/Frontier/PowerSlopeCoincidences.lean)), power-slope obstructions were established only at exact saturation $s = 0$ ($q = 1$). This note and its companion Lean module [`EighthNearSaturatedPowers.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthNearSaturatedPowers.lean) extend those obstructions across **all five** exceptional profiles $(1, 1, 1, 1)$ through $(1, 1, 1, 5)$ ($0 \le s \le 4$):

1. **No constant direction edge** ($m_i \ge 1$ for all six pairs) across all $1 \le q \le 5$.
2. **No three Möbius-of-power direction maps** from an optimal base head across all $0 \le s \le 4$: after ruling out `4 ∣ (a, b, c)` by a direct coset-union fresh-label count, the cyclic Möbius graph bound on $H = \mu_{2^{30}}$ (and $H^2 = \mu_{2^{29}}$) leaves exactly **six** boundary degree triples in two three-element families, and both families are unconditionally refuted over every field by a polynomial coset-sparsity obstruction.
3. **One Möbius-of-power slope plus two arbitrary companions**: across all $0 \le s \le 4$, at least one companion has degree at least **$7{,}479{,}697$** (within 1 of the exact-saturation floor $7{,}479{,}698$).
4. **Exact saturation of the nonscalar-antipode quotient**: whenever an $s = 4$ ($q = 5$) quartet falls into the nonscalar antipode of [`EighthDyadicHeadDirections.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthDyadicHeadDirections.lean), the quartet has $x_0 = x_3 = x_4 = 0$ and $x_2 = 8(2^{26} - 1)$ on $H$, forcing its quotient quartet on $H^2$ to be **exact-saturated** ($s' = 0$).

The unrestricted second-prime eighth-rate interval remains **$[671{,}088{,}640, 679{,}477{,}248]$**.

## 1. Optimal base head and near-saturated slack bounds (`0 ≤ s ≤ 4`)

Let $x_0, x_2, x_3, x_4$ count sites of $H$ covered by $0, 2, 3, 4$ of the four heads. For a chosen base head $0$, split $x_3 = y_3 + z_3$, where $y_3$ counts triple sites containing head $0$ and $z_3$ counts triple sites omitting head $0$. Summing $z_3$ over the four choices of base head gives $x_3$, so some base head satisfies $3 z_3 \le y_3$ (`exists_optimal_head`, Lean-checked).

Writing $e_{ij}$ for the number of double-only sites of $\{i, j\}$ and $m_i$ for the reduced degree of the projective direction $z_i$ of $W_i - W_0$ ($i \in \{1, 2, 3\}$), the near-saturated incidence identity $x_2 + 2(y_3 + z_3) + 3 x_4 + s = 4d + x_0$ together with the four triangle root budgets and $e_{jk} \le m_j + m_k$ yields (`near_saturated_bounds`, Lean-checked):
- $y_3 + z_3 + 2 x_4 + 2 x_0 \le 2s \le 8$ and $z_3 \le 2$,
- $d - 5 \le m_1 + m_2 + m_3 \le d + s \le d + 4$ (i.e. $m_1 + m_2 + m_3 \in [134{,}217{,}722,\, 134{,}217{,}731]$),
- $\sum_{1 \le j < k \le 3} (m_j + m_k - e_{jk}) \le 8$, so every unsigned pair coincidence loses at most $8$ sites from $m_j + m_k$,
- $e_{12} + e_{13} + e_{23} \ge 2d - 10$ and $e_{01} + e_{02} + e_{03} \ge 2d - 16$.

## 2. Constant-edge and quartic-factorization exclusions

- **No constant projective direction edge** (`no_constant_edge_q_ge_two`, `no_constant_edge_q_one`, Lean-checked):
  - For $2 \le q \le 5$, if one pair of heads has constant direction $z_0$, every non-shared site in $C_i \cup C_j$ contributes the same label $z_0$, losing at least $|C_i| + |C_j| - 2d - 1 \ge 4k - 5$ fresh slots across its two endpoints. Even with the full $20{,}607{,}410$ residual allowance, total labels are at most **$1{,}832{,}546{,}747 \ll 2n$**.
  - For $q = 1$ ($s = 0$), the opposite-direction involution $J$ is constant, so a constant edge forces its opposite edge to be constant too, losing at least $8k - 2$ fresh slots and capping total labels at **$1{,}631{,}220{,}152 \ll 2n$**.
- **No quartic direction triple** (`no_quartic_direction_triple`, Lean-checked): if all three reduced direction maps from head $0$ factor through $X^4$ on $H$, their combined image has size at most $3(n/4) = 6k$, covering every fresh label involving head $0$. The remaining off-$C_0$ fresh slots among $\{1, 2, 3\}$ add at most $2(n - c_0) - (e_{12} + e_{13} + e_{23}) + 3 x_0 \le 8k + 34$, capping total labels at **$1{,}899{,}655{,}636 \ll 2n$**.

## 3. Complete arithmetic classification of three power slopes (`0 ≤ s ≤ 4`)

Suppose $z_i(x) = M_i(x^{m_i})$ with positive degrees $a \ge b \ge c \ge 1$, $a \le d$, $d - 5 \le a + b + c \le d + 4$, and not all three divisible by $4$.
- When not all three are even, any odd-$\gcd$ pair $(u, v)$ with $u + v > 46{,}349$ exceeds the cyclic Möbius graph bound on $H$ (`mobius_cutoff_H`, Lean-checked), forcing a toric transition: either $u + v$ is a power of two, or $v \le 4$ and $u - v$ is a power of two (`eq_pow_two_of_near_gcd`, Lean-checked).
- When all three are even (so not all three are divisible by $4$), the reduced exponents $(a/2, b/2, c/2)$ obey the analogous cyclic Möbius graph bound on $H^2$ with cutoff $32{,}772$ and loss at most $4$ (`mobius_cutoff_H2`, `eq_pow_two_of_near_gcd_H2`, Lean-checked).

Exhausting both cases (`near_saturated_power_triples_odd`, `near_saturated_power_triples_even`, `near_saturated_power_triples`, Lean-checked) leaves **exactly six boundary triples**:
- **Family I**: $(2^{26} + k,\, 2^{26} - k,\, k)$ for $k \in \{1, 2, 3\}$,
- **Family II**: $(2^{27} - k,\, k,\, k)$ for $k \in \{1, 2, 3\}$.

## 4. Polynomial coset-sparsity refutation of Families I and II

In both surviving families, the two largest degrees $(m_1, m_2)$ sum to a power of two ($2Q = 2^{27}$ in Family I with $Q = 2^{26}$; $Q_2 = 2^{27}$ in Family II) while their difference is not a power of two, so the pair $(z_1, z_2)$ is in the reciprocal toric regime. Applying a constant projective row change over $\overline{\mathbb{F}}$ preserves degrees $\le d$ and all agreement sets in $H$, and puts the first two differences in the normal form:
$$
W_1 - W_0 = L_{01} (X^{m_1}, 1), \qquad W_2 - W_0 = L_{02} (\lambda, X^{m_2}), \qquad \lambda \ne 0.
$$
The second coordinate $L_{01} - X^{m_2} L_{02}$ vanishes on all $e_{12} \ge m_1 + m_2 - 8$ roots of $X^{m_1 + m_2} - \lambda$ in $H$. Letting $R$ be the monic squarefree polynomial of the missed roots of $X^{m_1 + m_2} - \lambda$ in $H$ ($\deg R \le 8$), there is $U \in \overline{\mathbb{F}}[X]$ with
$$
(L_{01} - X^{m_2} L_{02}) R = (X^{m_1 + m_2} - \lambda) U.
$$

- **Family II** ($m_1 = 2^{27} - k$, $m_2 = k$, $Q_2 = 2^{27}$, $\deg L_{01} \le k - 1 \le 2$):
  On each of the $8$ cosets $X^{Q_2} = \omega \in \mu_8$ of $H$, the equation $X^k L_{02} R = L_{01} R + (\lambda - X^{Q_2}) U$ specializes to $L_{01} R + (\lambda - \omega) U$. Because $U = 0$ or $\deg U < \deg R \le \deg(L_{01} R)$, this specialized polynomial is nonzero of degree at most $\deg L_{01} + \deg R \le 10$, capping $L_{02}$ at $8 \cdot 10 = 80$ roots in $H$ (`family_two_coset_obstruction`, Lean-checked). Yet `near_saturated_family_root_floors` gives $e_{02} \ge 134{,}217{,}712$, a contradiction.
- **Family I** ($m_1 = Q + k$, $m_2 = Q - k$, $Q = 2^{26}$, $\deg L_{01} \le Q - 1 - k$, $\deg L_{02} \le Q - 1 + k$):
  Degree comparison forces $U \ne 0$ and $\deg U < \deg R$. Splitting $L_{01} R = A + X^{Q-k} B$ at $Q - k$ identifies $A = -\lambda U$ and $B = L_{02} R + X^{Q+k} U$ with $B \ne 0$ and $\deg B < \deg R$. On each of the $16$ cosets $X^Q = \omega \in \mu_{16}$ of $H$, $X^k L_{01} R = X^Q B - \lambda X^k U$ restricts to $\omega B - \lambda X^k U$ of degree at most $k + \deg R$. Because $e_{01} \ge 67{,}108{,}848 > 16(k + \deg R) \le 176$, some $\omega_0 \in \mu_{16}$ satisfies $\omega_0 B = \lambda X^k U$, yielding
  $$
  L_{01} R = \frac{\lambda}{\omega_0}(X^Q - \omega_0) U, \qquad L_{02} R = -\frac{1}{\omega_0} X^k (\omega_0 X^Q - \lambda) U.
  $$
  Since $R$ has $\deg R > \deg U$ roots in $H$, some root $r_0 \in H$ of $R$ satisfies $U(r_0) \ne 0$. Evaluating both identities at $r_0$ forces $r_0^Q = \omega_0$ and $\omega_0 r_0^Q = \lambda$, so $\lambda = \omega_0^2$. Both $L_{01}$ and $L_{02}$ therefore vanish on all $Q - \deg R \ge 67{,}108{,}856$ points of the coset $X^Q = \omega_0$ outside the roots of $R$ (`family_one_coset_obstruction`, Lean-checked), contradicting $y_3 + x_4 \le 8$.

## 5. One power slope plus two arbitrary companions (`0 ≤ s ≤ 4`)

Let $z_1 = M(X^a)$ ($a > 0$) and let $z_2, z_3$ be arbitrary nonconstant rational maps of degrees $m_2, m_3 \le B$. Apply `PowerSlopeCoincidences.rational_bound` on $H$ to $R_j = M^{-1} z_j$ ($j \in \{2, 3\}$):
- **Direct branch**: if either $z_2$ or $z_3$ satisfies the multiplicative translation bound on $H$, its unsigned coincidences with $z_1$ satisfy $e_{1j} \ge m_1 + m_j - 8 \ge (d - 5) - B - 8 = d - 13 - B$, forcing $B \ge 7{,}479{,}697$ (`eighth_near_saturated_companion_direct`, Lean-checked).
- **Double-symmetry branch**: if both fail the bound on $H$, each has a nonidentity multiplicative symmetry in the cyclic $2$-group $H$, hence obeys $R_j(-X) = (-1)^a R_j(X)$ alongside $z_1$:
  - If $a$ is **even**, all three maps are antipode-invariant ($z_i(-X) = z_i(X)$), putting the quartet in the scalar antipode of `EighthDyadicHeadDirections`, whose `antipodal_mass` caps total fresh head labels at $1{,}879{,}048{,}348$ ($+ 20{,}607{,}410 \ll 2n$), impossible.
  - If $a$ is **odd**, all three maps transform under the same nonidentity projective involution $w \mapsto M(-M^{-1}(w))$, putting the quartet in the nonscalar antipode of `EighthDyadicHeadDirections` (`antipode_forces_quotient`: $r = 0$, $s = 4$, $d' = 2^{26} - 1$). By `nonscalar_antipode_exact_saturation` (Lean-checked), this forces $x_0 = x_3 = x_4 = 0$ and $x_2 = 8 d'$ on $H$, making the quotient quartet on $H^2$ ($|H^2| = 2^{29}$, degree $d' = 2^{26} - 1$) **exact-saturated** ($s' = 0$). Downstairs on $H^2$, $z_1$ descends to a power slope and $z_2, z_3$ descend to rational maps of degrees $m_2', m_3' \le B'$ with $2 B' \le B + 1$. By the exact-saturation argument of [`saturated-power-translations.md`](saturated-power-translations.md) on $H^2$, at least one companion downstairs obeys the $H^2$ translation bound, forcing $B' \ge 3{,}739{,}849$ and hence again $B \ge 2 B' - 1 \ge 7{,}479{,}697$ (`eighth_near_saturated_companion_quotient`, `eighth_near_saturated_companion`, Lean-checked).

## Verification ledger

- **Lean-checked (axiom-clean, zero `sorry`)**: [`ArkLib/Research/ProximityGap/Frontier/EighthNearSaturatedPowers.lean`](../../../ArkLib/Research/ProximityGap/Frontier/EighthNearSaturatedPowers.lean) — all 20 public theorems (`exists_optimal_head`, `near_saturated_bounds`, `near_saturated_family_root_floors`, `no_constant_edge_q_ge_two`, `no_constant_edge_q_one`, `no_quartic_direction_triple`, `mobius_cutoff_H`, `mobius_cutoff_H2`, `eq_pow_two_of_near_gcd`, `eq_pow_two_of_near_gcd_H2`, `near_saturated_power_triples_odd`, `near_saturated_power_triples_even`, `near_saturated_power_triples`, `family_two_coset_obstruction`, `family_one_coset_obstruction`, `family_one_and_two_concrete_contradictions`, `nonscalar_antipode_exact_saturation`, `eighth_near_saturated_companion_direct`, `eighth_near_saturated_companion_quotient`, `eighth_near_saturated_companion`) verified with `#print axioms` $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$.
- **Reproducible probe**: [`scripts/probes/probe_eighth_near_saturated_powers.py`](../../../scripts/probes/probe_eighth_near_saturated_powers.py) independently checks the slack polytope over all $0 \le s \le 4$, exhausts both $r = 0$ and $r = 1$ power-slope triples, verifies concrete polynomial coset-sparsity examples over finite fields, and verifies both branches of the companion floor $7{,}479{,}697$.
- **Written-only geometric bridges**: connecting the projective row normalization $M_2^{-1}$ and the cyclic-group descent from `PowerSlopeCoincidences.rational_bound` / `EighthDyadicHeadDirections` to the algebraic hypotheses of `EighthNearSaturatedPowers.lean`.
