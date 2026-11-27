# Universal Dyadic-Eigenspace Pullback Exclusion across $\mu_{64}, \mu_{128}, \dots, \mu_{2^{30}}$

## Summary

This note accompanies [`QuarterDyadicEigenspaceExclusion.lean`](../../../ArkLib/Research/ProximityGap/Frontier/QuarterDyadicEigenspaceExclusion.lean) and [`probe_quarter_dyadic_eigenspace.py`](../../../scripts/probes/probe_quarter_dyadic_eigenspace.py) (+ `.cpp`), eliminating **all** non-degenerate dyadic rotational eigenspace pullbacks across the entire tower of subgroups $\mu_{32 \cdot 2^s} \subseteq \mu_{2^{30}}$ ($1 \le s \le 25$, from $\mu_{64}$ all the way to $\mu_{2^{30}}$):
$$P(x) = x^a A(x^{2^s}), \qquad Q(x) = x^b B(x^{2^s}), \qquad a \not\equiv b \pmod{2^s}, \quad A, B \subset \mu_{32} \text{ disjoint}$$
over both designated primes $p_1 = 2^{30}(2^{128}+192)+1$ and $p_2 = 2^{30}(2^{129}+13)+1$ (indeed over every prime $p > 2^{150}$ with $32 \cdot 2^s \mid p - 1$).

Specifically:
1. **Every higher dyadic level $s' \ge 2$** ($\mu_{128}, \mu_{256}, \dots, \mu_{2^{30}}$ after dividing out $g = \gcd(a - b, 2^s)$): **zero computer search!** For **every** disjoint $A, B \subset \mu_{32}$ with $|A|, |B| \le 15$ (covering rate $1/4$, rate $1/2$, and all lower rates simultaneously) and every $\lambda \in \mathbb{F}_p^\times$, the polynomial $P(x) - \lambda Q(x)$ has **at most ONE root per $\mu_{32}$-coset** — at most $2^s$ roots total out of $32 \cdot 2^s$ (only $1/32$ of the domain, capping the quarter-rate score at $9 \cdot 2^s \ll 18 \cdot 2^s$).
2. **Antipodal opposite-parity level $s' = 1$** ($\mu_{64}$: $P(x) = A(x^2)$, $Q(x) = x B(x^2)$):
   - All **57** degree pairs $(d_1, d_2) \in \{0,\dots,7\}^2$ with $d_1 \ne d_2 + 1$ (and all $d_1 = d_2 + 1 \le 6$) are eliminated with **zero computer search** via the exact unit-circle phase law (`dyadic_eigenspace_s1_all_except_76`), keeping the $\mu_{64}$ root score $\le 36$. In particular, $(7, 7)$ has at most **2 roots** in $\mu_{64}$ (1 even, 1 odd)!
   - The **sole** constant-phase pair $(d_1, d_2) = (7, 6)$ forces $r(P - \lambda Q) \ge 14$ in $\mu_{64}$, hence $\ge 7$ same-parity roots in $\mu_{32}$ (`dyadic_eigenspace_s1_76_forces_seven_same_parity`), which lifts to characteristic zero ($< 2^{120} < p_1 < p_2$) and has **zero** ternary solutions across all `6,903` orbits of $\binom{32}{7} = 3{,}365{,}856$ at both $m = 101$ and $m = 103$.

Together with `mu32-quarter-list-threshold.md` (same-parity antipodal $(+,+)$ and $(-,-)$) and `QuarterMu64DihedralExclusion.lean` (all degree-$2^{25}$ dihedral reflections), this **completely eliminates all four antipodal eigenspace parity patterns `(+,+), (-,-), (+,-), (-,+)` on $\mu_{64}$** and the entire rotational eigenspace tower above $\mu_{32}$!

## Proof Architecture

### 1. Norm Lift in $\mathbb{Q}(\zeta_{32})$ (`< 2^{120}` for $d \le 7$, `< 2^{150}` for $d \le 15$)

Reducing by $g = \gcd(a - b, 2^s) = 2^t$ ($0 \le t < s$), set $y = x^{2^t} \in \mu_{32 \cdot 2^{s'}}$ with $s' = s - t \ge 1$ and $r := (a - b)/2^t$ **odd**. Partition $\mu_{32 \cdot 2^{s'}}$ into the $2^{s'}$ cosets of $\mu_{32}$. For any two distinct roots $y_1 \ne y_2$ of $y^r A(y^{2^{s'}}) = \lambda B(y^{2^{s'}})$ in the same $\mu_{32}$-coset:
- $u := y_2 / y_1 \in \mu_{32} \setminus \{1\}$, and $z_1 := y_1^{2^{s'}} \ne y_2^{2^{s'}} =: z_2$ (otherwise $u^{2^{s'}} = 1$ and $u^r = 1 \implies u^{\gcd(2^{s'}, r)} = u = 1$).
- In $\mathbb{F}_p^\times$, $u^r \frac{A(z_2) B(z_1)}{A(z_1) B(z_2)} = 1$.
- Lifting to $\mathbb{Q}(\zeta_{32})$: $\rho := u^r \frac{A(z_2) B(z_1)}{A(z_1) B(z_2)}$ is a $\{2\}$-unit in $\mathbb{Q}(\zeta_{32})$ whose absolute value $|\sigma(\rho)|$ in every complex embedding $\sigma$ is identical to $|\sigma(\frac{A(z_2) B(z_1)}{A(z_1) B(z_2)})|$ (since $|\sigma(u)| = 1$).
- Pure-integer outward-rounded interval arithmetic (`probe_quarter_dyadic_eigenspace.py`) certifies uniformly over all disjoint $A, B \subset \mu_{32}$:
  - $|N_{\mathbb{Q}(\zeta_{32})/\mathbb{Q}}(1 - \rho)| < 2^{120} < p_1 < p_2$ for all $|A|, |B| \le 7$;
  - $|N_{\mathbb{Q}(\zeta_{32})/\mathbb{Q}}(1 - \rho)| < 2^{150} < p_1 < p_2$ for all $|A|, |B| \le 15$.
- By `norm_lift_eq_zero`, $\rho = 1$ holds **identically in $\mathbb{C}$**.

### 2. Exact Complex Unit-Circle Phase Law (Axiom-Clean Lean)

Formalized in `QuarterDyadicEigenspaceExclusion.lean`:
- `unit_circle_diff_sq`: $(z - a)^2 = -a z \cdot \operatorname{normSq}(z - a)$ for all $z, a \in S^1$.
- `unit_circle_prod_sq`: $\big(\prod_{a \in A}(z - a)\big)^2 = (-1)^{|A|} (\prod_{a \in A} a) z^{|A|} \prod_{a \in A} \operatorname{normSq}(z - a)$.
- `unit_circle_phase_power_eq_one`: Squaring $u^r A(z_2) B(z_1) = A(z_1) B(z_2)$ with $z_2 = u^{2^{s'}} z_1$ cancels the common factor and forces a strictly positive real multiple of $u^{2r + 2^{s'}(|A| - |B|)}$ to equal $1$, hence
  $$u^{2r + 2^{s'}(|A| - |B|)} = 1.$$
- `dyadic_eigenspace_s_ge_2_unique_in_coset`: Whenever $s' \ge 2$ and $r$ is odd, $v_2(2r + 2^{s'}(|A| - |B|)) = 1$, forcing $\gcd(32, |E|) = 2 \implies u^2 = 1 \implies u^{2^{s'}} = 1$, contradicting $z_1 \ne z_2$!
- `dyadic_eigenspace_s1_phase_order` & `dyadic_eigenspace_s1_all_except_76`: For $s' = 1$, $u^{2 \gcd(16, |d_1 - d_2 - 1|)} = 1$, giving $\le \gcd(16, |d_1 - d_2 - 1|)$ roots per coset and score $\le 36$ for all 57 non-$(7,6)$ degree pairs in $\{0,\dots,7\}^2$.

### 3. Exhaustion of the Sole Constant-Phase Pair $s' = 1, (7, 6)$

For $(d_1, d_2) = (7, 6)$, `dyadic_eigenspace_s1_76_forces_seven_same_parity` forces $\ge 7$ same-parity roots $C \subset \mu_{32}$. By `unit_log_independence_to_kernel_8`, the ternary vector $w = \mathbf{1}_A - \mathbf{1}_B$ lies in the modular kernel of the $49 \times 25$ system ($6 \times 8 = 48$ cyclotomic-unit difference equations plus $\sum_z w_z = 1$). `probe_quarter_dyadic_eigenspace_sieve.cpp` exhausts all `6,903` rotation+Galois orbits (verified orbit sum $\binom{32}{7} = 3{,}365{,}856$, max consistent nullity `4`) at both $m = 101$ and $m = 103$, finding **`0` ternary solutions**!

## Honesty Boundary

- **100% axiom-clean Lean (`QuarterDyadicEigenspaceExclusion.lean`):** All 11 theorems (complex unit-circle phase law, universal $s \ge 2$ coset uniqueness, complete $s = 1$ score table for all 63 non-$(7,6)$ pairs, $(7,6)$ 7-root pigeonhole, norm-lift zero criterion, 8-unit modular kernel bridge, and exact prime/orbit headroom) compile with 0 `sorry`, 0 warnings, and `#print axioms` $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$.
- **Deterministic exact-integer scripts (`probe_quarter_dyadic_eigenspace.py` + `.cpp`):** Certify the uniform `< 2^{120}` / `< 2^{150}` $\mathbb{Q}(\zeta_{32})$ norm bounds (pure integer arithmetic), 8×8 regulator non-vanishing, and the 6,903-orbit modular rank sieve at $m = 101, 103$.
