# Large-characteristic Wronskian gcd bound and sharp split-pencil suborbits

Let $H = \mu_n$, $n = 2^{30}$, and $D = n/4 - 2 = 268{,}435{,}454$ in either designated prime field $\mathbb{F}_{p_1}$ or $\mathbb{F}_{p_2}$ (in fact, any prime $p > 2 n D = 576{,}460{,}748{,}008{,}456{,}192$). Suppose $R = P/Q$ is a hypothetical degree-$D$ split pencil whose fibers above $0, 1, \infty$ consist of $D$ distinct points each in $H$.

Using a self-contained large-characteristic Wronskian bound on the three-dimensional space $\operatorname{Span}\{u-1, v-1, uv-1\}$ (replacing Corvaja–Zannier's Proposition 2, which was designed for small characteristic), we sharpen every suborbit, inner-degree, genus, and branch-order obstruction by nearly a factor of five:

- **Subdegree floor:** Every nontrivial orbit of a sheet stabilizer of $R$ (or of any rational inner factor $T$) has size at least **44,739,240** (up from 9,085,508).
- **Permutation rank:** $R$ has at most **6** nontrivial suborbits and permutation rank at most **8** (down from 29 and 31).
- **Proper inner degrees eliminated:** Both **$19{,}173{,}961$** (outer degree 14) and **$38{,}347{,}922$** (outer degree 7) are completely impossible. The only remaining proper inner degrees are **$2$** and **$D/2 = 134{,}217{,}727$** (outer degree 2).
- **Whole-pencil orbifold excess:** $E_R \ge \frac{268{,}435{,}414}{671{,}088{,}649} > 0.399999932$ unconditionally (up from $0.070063$). This rules out every $(2, b, c)$ signature with $3 \le b \le 9$ and arbitrary $c$, every $(3, 3, c)$ for arbitrary $c$, every $(2, 10, c)$ with $c \le 14{,}716{,}856$, every $(3, 4, c \le 59)$, $(3, 5, c \le 14)$, $(4, 4, c \le 9)$, and every 4-branch $(2, 2, 2, c \le 9)$. For the remaining $s = 2$ inner stage ($t = 134{,}217{,}727$), $E \ge \frac{268{,}435{,}426}{268{,}435{,}465} > 0.999999854$, so any 3-branch cover has all three inertia orders at least $6{,}882{,}961$.

Lean formalizes the valuation-subspace comparison lemma, the Vandermonde nonvanishing criterion, the exact rectangle pole-zero cancellation identity, the abstract Wronskian and Kummer pullback inequalities, and all production numerical and signature exclusions. The curve-theoretic invocation of the product formula for meromorphic sections of $(\Omega^1)^{\otimes \binom{M}{2}}$ and tame logarithmic Riemann–Hurwitz is written below. [Lean formalization](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSplitWronskianSuborbits.lean) · [Independent verification](../../../scripts/probes/probe_quarter_split_wronskian_suborbits.py) · [Previous suborbit note](quarter-split-suborbits.md)

## Self-contained Wronskian gcd bound in large characteristic

Let $X'$ be a smooth projective curve of genus $g'$ over an algebraically closed field $K$ of characteristic $p$, and let $u, v \in K(X')^\times$ be nonconstant rational functions with $K(X') = K(u, v)$, degrees $H_u = \deg(u)$ and $H_v = \deg(v)$, and zeros and poles contained in a finite set $S' \subset X'$. Let $h, k \ge 1$ be integers satisfying $k < H_u$ (or $h < H_v$) and $h H_u + k H_v < p$. Put $M = hk + h + k$ and $Z' = \{P \in X' \setminus S' : u(P) = v(P) = 1\}$. For $P \in Z'$, write $d_P = \min(v_P(u-1), v_P(v-1)) \ge 1$. Then
\[
  \sum_{P \in Z'} d_P \;\le\; \frac{h H_u + k H_v}{M} + \frac{M - 1}{2}\big(2g' - 2 + |S'|\big).
\]

**Proof.**
1. *Linear independence.* The $M + 1 = (h+1)(k+1)$ monomials $u^i v^j$ ($0 \le i \le h, 0 \le j \le k$) are linearly independent over $K$: any nontrivial relation $\sum_{j=0}^k P_j(u) v^j = 0$ would give $H_u = [K(u, v) : K(u)] \le k$, contradicting $k < H_u$. Hence the hyperplane
   \[
     W_1 = \operatorname{Span}_K \{u^i v^j - 1 : 0 \le i \le h,\, 0 \le j \le k,\, (i, j) \ne (0, 0)\}
   \]
   has dimension $M$.

2. *Nonvanishing of the ordinary Wronskian.* Every $f \in W_1$ belongs to $\mathcal{L}(E)$ for the effective divisor $E = h(u)_\infty + k(v)_\infty$ of degree $h H_u + k H_v < p$. Fix any $P \in X' \setminus \operatorname{supp}(E)$ and a $P$-adapted basis $\tilde{f}_1, \dots, \tilde{f}_M$ of $W_1$ with strictly increasing valuations $0 \le e_1 < \dots < e_M$ at $P$. Since $\tilde{f}_M \in \mathcal{L}(E) \setminus \{0\}$, we have $e_M \le \deg E < p$. In a local uniformizer $\pi$ at $P$, the leading coefficient of $W_\pi(\tilde{f}_1, \dots, \tilde{f}_M)$ is a nonzero multiple of the Vandermonde determinant $\prod_{r < s} (e_s - e_r) \not\equiv 0 \pmod p$. Choose any $t \in K(X')$ with $dt \ne 0$ (e.g. $t = u$ since $H_u < p$). Then $\Omega = W_t(f_1, \dots, f_M) (dt)^{\binom{M}{2}}$ is a nonzero meromorphic section of $(\Omega_{X'}^1)^{\otimes \binom{M}{2}}$, independent of the choice of basis up to $K^\times$.

3. *Local orders.* At every $P \in X'$ with local uniformizer $\pi$ and $P$-adapted basis valuations $e_1 < \dots < e_M$, differentiating term-by-term gives $\operatorname{ord}_P(\Omega) \ge \sum_{m=1}^M e_m - \binom{M}{2}$.
   - Outside $S' \cup Z'$, regularity gives $0 \le e_1 < \dots < e_M$, so $\operatorname{ord}_P(\Omega) \ge 0$.
   - At $P \in Z'$, every $f \in W_1$ vanishes to order at least $d_P$ (since $u^i v^j - 1$ lies in the ideal $\langle u - 1, v - 1 \rangle$), so $d_P \le e_1 < \dots < e_M$ and $\operatorname{ord}_P(\Omega) \ge M d_P$.
   - At $Q \in S'$, let $e_u = v_Q(u)$ and $e_v = v_Q(v)$. The monomials $u^i v^j$ span $V \supset W_1$ with valuations $a_1 \le \dots \le a_{M+1}$ given by $\{i e_u + j e_v\}$. By the non-Archimedean valuation-subspace comparison lemma (proved in Lean), $e_m \ge a_m$ for every $1 \le m \le M$. Since $a_{M+1} = \max_{0 \le i \le h, 0 \le j \le k}(i e_u + j e_v) = h \max(0, e_u) + k \max(0, e_v)$, we obtain
     \[
       \operatorname{ord}_Q(\Omega) \;\ge\; \sum_{i=0}^h \sum_{j=0}^k (i e_u(Q) + j e_v(Q)) - h \max(0, e_u(Q)) - k \max(0, e_v(Q)) - \binom{M}{2}.
     \]

4. *Global sum.* Since $\sum_{Q \in S'} e_u(Q) = \sum_{Q \in S'} e_v(Q) = 0$ and $\sum_{Q \in S'} \max(0, e_u(Q)) = H_u$, $\sum_{Q \in S'} \max(0, e_v(Q)) = H_v$, summing over all $P \in X'$ against $\sum_{P \in X'} \operatorname{ord}_P(\Omega) = \binom{M}{2}(2g' - 2)$ gives
   \[
     M \sum_{P \in Z'} d_P - (h H_u + k H_v) - \binom{M}{2} |S'| \;\le\; \binom{M}{2}(2g' - 2),
   \]
   and dividing by $M$ yields the bound. $\square$

## Application to the quarter-rate split pencil

Let $R = V \circ T$ and let $X$ be the smooth projective normalization of a nontrivial (multiplicatively independent) component of $T(x) = T(y)$ of bidegree $(a, a)$. Put $u = x^n$, $v = y^n$, and let $X'$ have function field $K(u, v)$ with Kummer extension degree $c = [K(X) : K(X')]$. As in the previous suborbit note, $c \le 2n$ by the source-symmetry theorem. Since $p \nmid n$, $X \to X'$ is tame and unramified outside $S'$, so logarithmic Riemann–Hurwitz gives $\chi(X) = c \chi(X')$, while $|Z| \le c |Z'|$, $c H_u = c H_v = n a$.

To verify $H_u \ge 2$ without invoking Corvaja–Zannier Theorem 2:
- For $a \ge 3$, $|Z'| \ge 3 D a / c \ge 9 D / (2n) > 1$, so $u(P) = 1$ has at least two distinct solutions on $X'$, hence $H_u \ge 2$.
- For $a = 2$, $H_u = 1$ would force $c = 2n$, making the bidegree-$(2, 2)$ component $X$ invariant under a cyclic scaling group $(x, y) \mapsto (\zeta x, \zeta^r y)$ of order $n = 2^{30}$; comparing exponents $i + rj \pmod{2^{30}}$ on $0 \le i, j \le 2$ forces all surviving monomials to be collinear, contradicting multiplicative independence.

Take $h = k = 1$ ($M = 3$), which is globally optimal across all rectangles $[0, h] \times [0, k]$ and vanishing orders $T \ge 1$. The characteristic condition $H_u + H_v \le 2 n D = 576{,}460{,}748{,}008{,}456{,}192 < 2^{59} < p_1 < p_2$ holds with nearly 100 bits to spare. Multiplying the $X'$ inequality by $c$ cancels $c$ identically and yields
\[
  3 D a \;\le\; \frac{2}{3} n a + \chi(X).
\]
Hence $\chi(X) \ge \lambda a$ with $\lambda = (9D - 2n)/3 = 268{,}435{,}438/3 \approx 89{,}478{,}479.33$. Since $\chi(X) \le 2 a^2$, this gives $a \ge 44{,}739{,}240$, at most $6$ nontrivial suborbits, and eliminates every proper inner degree $2 < t < 134{,}217{,}727$ dividing $D = 2 \cdot 7 \cdot 73 \cdot 262657$ (in particular both $19{,}173{,}961$ and $38{,}347{,}922$).

Combining $\lambda = 268{,}435{,}438/3$ with the quadratic pullback and variance bound $(2g(Y) - 2)(E + 2) \le 2(m - 1)^2 E$ gives the three surviving stage bounds:

| Stage $(s, h, m)$ | Exact excess floor on $E$ | Lower bound on $g(Y)$ | Consequence |
| --- | ---: | ---: | --- |
| $(2, 1, 134{,}217{,}727)$ | $\frac{268{,}435{,}426}{268{,}435{,}465} > 0.999999854$ | $6{,}004{,}798{,}742{,}593{,}547$ | Any 3-branch cover has all three inertia orders $\ge 6{,}882{,}961$. |
| $(1, 2, 134{,}217{,}727)$ | $\frac{268{,}435{,}414}{671{,}088{,}649} > 0.399999932$ | $3{,}002{,}399{,}237{,}079{,}048$ | Excludes all $(2, 3..9, c)$, $(3, 3, c)$, $(2, 10, c \le 14.7\text{M})$, etc. |
| $(1, 1, 268{,}435{,}454)$ | $\frac{134{,}217{,}713}{335{,}544{,}323} > 0.399999951$ | $12{,}009{,}597{,}529{,}926{,}331$ | Same whole-pencil exclusions, $g(Y) > 1.2 \times 10^{16}$. |

Charging the outer degree $s \in \{1, 2\}$ gives $E_R \ge E / s \ge \frac{268{,}435{,}414}{671{,}088{,}649} > 0.399999932$ unconditionally for the whole pencil $R$.

## Necessity of the large-characteristic hypothesis

The companion verification script checks an explicit degree-$7$ split pencil on $\mu_{32}$ over $\mathbb{F}_{97}$ ($p = 97 > 3n = 96$): with primitive 32nd root $w = 5^3 \equiv 28 \pmod{97}$, the disjoint $7$-sets $A = \{3, 4, 17, 19, 21, 24, 25\}$, $B = \{2, 11, 14, 22, 23, 28, 31\}$, $C = \{0, 5, 6, 12, 18, 27, 30\}$ satisfy $L_A(X) - 16 L_B(X) = -15 L_C(X)$ in $\mathbb{F}_{97}[X]$. Thus split pencils exist in small tame prime characteristic $p > 3n$ whenever $p^{D-1} \ll 4^n$, confirming that any complete refutation at the designated primes must use either large-$p$ bounds ($p \gg n$) or prime-specific arithmetic.
