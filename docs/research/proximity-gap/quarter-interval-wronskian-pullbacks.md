# Wronskian pullback exclusions across the entire 33.55M quarter-rate interval

Let $H = \mu_n$, $n = 2^{30}$, and $D = n/4 - 2 = 268{,}435{,}454$ in either designated prime field $\mathbb{F}_{p_1}$ or $\mathbb{F}_{p_2}$ (or any prime $p > 6 n D \approx 1.73 \times 10^{18}$). By the three-head root-score theorem, every three-head quarter-rate attack beating the known cubic ceiling at **480,946,859 errors** corresponds to a reduced rational map $R = P/Q$ of degree $m \le D$ whose three fibers $W = R^{-1}(\{0, 1, \infty\}) \cap H$ achieve score
\[
  S(R) = 2|W| - 3m \;\ge\; 603{,}979{,}777 = \frac{9}{16} n + 1.
\]
Through **469,762,048 errors**, every unrestricted MCA overrun requires such a three-head map with $S(R) \ge 671{,}088{,}641 = \frac{5}{8} n + 1$. Previously only geometrically Galois maps were excluded across this interval. [Three-head root score](quarter-three-head-root-score.md) · [Galois score ceiling](quarter-root-score-symmetry.md)

Combining a new elementary **Kummer determinant height floor** with the large-characteristic Wronskian gcd bound gives uniform inner-degree exclusions across the entire 33,554,431-error open interval, for arbitrary partial fibers and arbitrary dihedral symmetry groups:

- **Beating 480,946,859 ($S \ge 603{,}979{,}777$):** Every non-dihedral inner rational factor $T$ of $R = V \circ T$ has **$\deg T \ge 12{,}463{,}075$**.
- **Unrestricted attacks through 469,762,048 ($S \ge 671{,}088{,}641$):** Every non-dihedral inner rational factor $T$ of $R = V \circ T$ has **$\deg T \ge 19{,}173{,}962$**.
- **Zero dependence on Corvaja–Zannier Theorem 2:** The Kummer determinant floor forces $H_i \ge 108$ whenever the scaling symmetry group has order $q \le 2$, eliminating even the auxiliary `a > 4` citation from the full split-pencil suborbit theory.

Lean formalizes the Kummer determinant divisibility and packing lemmas, the height floors, the AM-GM score reduction, the concave-quadratic elimination for $w \ge 3$, and both concrete interval theorems. The curve-theoretic Kummer extension, off-diagonal pair decomposition, and Wronskian product-formula application are written below. [Lean formalization](../../../ArkLib/Research/ProximityGap/Frontier/QuarterIntervalWronskianPullbacks.lean) · [Independent verification](../../../scripts/probes/probe_quarter_interval_wronskian_pullbacks.py) · [Full-split Wronskian suborbits](quarter-split-wronskian-suborbits.md)

## Kummer determinant height floor

Let $X$ be an irreducible curve over $K = \overline{\mathbb{F}}_p$ ($p \nmid n = 2^e$), with $x, y \in K(X)^\times$ multiplicatively independent modulo $K^\times$. Put $u = x^n$, $v = y^n$, let $X'$ have function field $K(u, v)$, and set $c = [K(X) : K(X')]$, $H_u = \deg_{X'}(u)$, $H_v = \deg_{X'}(v)$. Then
\[
  n^2 \;\le\; 4 c H_u^2 H_v^2.
\]
In particular, when $H_u = H_v = H$:
1. If $c \le q n$, then $n \le 4 q H^4$. At $n = 2^{30}$, this forces $H \ge 108$ for $q \le 2$, $H \ge 4$ for $q \le 2^{21}$, and $H \ge 3$ for $q \le 2^{23}$.
2. Unconditionally (using $c H = n a$ for bidegree $(a, a)$), $n \le 4 a H^3$.

**Proof.** Since $p \nmid n$ and $\mu_n \subset K$, Kummer theory identifies $\operatorname{Gal}(K(X)/K(X'))$ with $\Gamma = \langle u, v \rangle (K(X')^\times)^n / (K(X')^\times)^n$ of order $c$. The surjective homomorphism $\psi : (\mathbb{Z}/n\mathbb{Z})^2 \to \Gamma$, $(r, s) \mapsto u^r v^s$, has kernel $K_\psi$ of cardinality $n^2 / c$. Since $n = 2^e$, let $d = 2^v \mid n$ be the largest power of two dividing both coordinates of every element of $K_\psi$, and set $N' = n / d = 2^{e - v}$. Every element of $K_\psi$ lies in $(d\mathbb{Z}/n\mathbb{Z})^2$, so $n^2 / c = |K_\psi| \le (N')^2$. On the other hand, some $(r, s) \in K_\psi$ has $r = d r', s = d s'$ with $r'$ or $s'$ odd. The relation $u^r v^s = w^n$ in $K(X')^\times$ gives
\[
  r' e_u(q) + s' e_v(q) \equiv 0 \pmod{N'}
\]
for every zero or pole $q \in S'$ of $u, v$, where $e_u(q) = v_q(u)$, $e_v(q) = v_q(v)$. Since $\gcd(r', s', N') = 1$, $N'$ divides every $2 \times 2$ determinant $\Delta(q_1, q_2) = e_u(q_1) e_v(q_2) - e_u(q_2) e_v(q_1)$. Because $u, v$ are multiplicatively independent, $\operatorname{div}(u)$ and $\operatorname{div}(v)$ are not proportional over $\mathbb{Q}$, so some $\Delta(q_1, q_2) \ne 0$. Since $|e_u(q)| \le H_u$ and $|e_v(q)| \le H_v$, we have $0 < |\Delta(q_1, q_2)| \le 2 H_u H_v$, forcing $N' \le 2 H_u H_v$. Combining $n^2 \le c (N')^2$ with $N' \le 2 H_u H_v$ gives $n^2 \le 4 c H_u^2 H_v^2$. $\square$

## Uniform inner-degree exclusion for partial three-head pencils

Let $R = V \circ T$ with $\deg T = t$, $\deg V = s$, $m = s t \le D$, and $S(R) = 2|W| - 3m \ge S_{\min}$. By `QuarterRootScoreSymmetry.lean`, since $S_{\min} > 3{,}960{,}117$, every deck transformation of $T$ belongs to the dihedral group $D_{2n}$ of scalings $x \mapsto \alpha x$ and scaled reciprocals $x \mapsto \alpha / x$ with $\alpha \in H$. Put $d_{\mathrm{aut}} = |\operatorname{Aut}(T)| = 2^r \mid t$, let $q \le d_{\mathrm{aut}}$ be the number of scaling deck transformations, and write $t = d_{\mathrm{aut}} w$. A non-dihedral inner factor has $w \ge 2$.

Let $u_1, \dots, u_K$ ($K \le 3s$) be the sizes of the intersections of $H$ with the $T$-fibers over $V^{-1}(\{0, 1, \infty\})$, so $\sum u_j = |W|$. Cauchy–Schwarz gives $\sum u_j(u_j - 1) \ge |W|^2/(3s) - |W| = (|W|^2/(3m)) t - |W|$. Removing the $d_{\mathrm{aut}} - 1$ nonidentity deck-transformation graphs (each contributing at most $|W|$ ordered pairs) leaves at least
\[
  |Z_{\mathrm{nontoric}}| \;\ge\; d_{\mathrm{aut}} \left(\frac{|W|^2}{3m} w - |W|\right)
\]
ordered pairs on the multiplicatively independent components $X_i$ of $T(x) = T(y)$, whose bidegrees $(a_i, a_i)$ sum to $A = t - d_{\mathrm{aut}} = d_{\mathrm{aut}}(w - 1)$. Monotonicity in $|W| \ge (S_{\min} + 3m)/2$ and $m \le D$ yields
- $d_{\mathrm{aut}}(S_{\min}^2/(6D) + S_{\min}/2)$ when $w = 2$, and
- $d_{\mathrm{aut}}(S_{\min}(w - 1) - (3D - S_{\min})/2)$ when $w \ge 3$.

Each component $X_i$ satisfies $c_i \le q n$ (since the kernel of $(x, y) \mapsto \alpha x$ in $\operatorname{Gal}(K(X_i)/K(X_i'))$ consists of scaling deck transformations of $T$). Applying the large-characteristic Wronskian bound with rectangle $[0, h] \times [0, k]$ ($M = hk + h + k$, valid whenever $k < H_i$ and $(h + k) n D < p$) and summing $\sum \chi(X_i) \le 2 \sum a_i^2 \le 2 A^2$ gives
\[
  |Z_{\mathrm{nontoric}}| \;\le\; \frac{h + k}{M} n A + (M - 1) A^2.
\]
- **At $S_{\min} = 603{,}979{,}777$:** Taking $(h, k) = (3, 3)$ ($M = 15$, valid for all $r \le 21$ since $H_i \ge 4 > 3$) gives $t \ge 14{,}140{,}798$ for $w = 2$ and $t \ge 12{,}463{,}075$ uniformly for all $w \ge 3$ by the concave-quadratic bound; at $r = 22$, $(h, k) = (4, 2)$ ($M = 14$, valid since $H_i \ge 3 > 2$) kills $w = 2$, while $w \ge 3$ gives $t \ge 3 \cdot 2^{22} = 12{,}582{,}912$; and $r \ge 23, w \ge 2$ gives $t \ge 2^{24} = 16{,}777{,}216$.
- **At $S_{\min} = 671{,}088{,}641$:** Taking $(h, k) = (2, 2)$ ($M = 8$, valid for all $r \le 23$ since $H_i \ge 3 > 2$) gives $t \ge 22{,}369{,}624$ for $w = 2$ and $t \ge 19{,}173{,}962$ uniformly for all $w \ge 3$; and $r \ge 24, w \ge 2$ gives $t \ge 2^{25} = 33{,}554{,}432$.
