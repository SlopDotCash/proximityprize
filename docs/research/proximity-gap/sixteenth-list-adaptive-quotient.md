# Site-dependent multiplicities in the second jet interpolation

At rate $1/16$ the second named prime has all-center list safety through **810,406,368 errors**, hence its first failing error count is at least **810,406,369**. This holds at every positive interleaving width on every injective grid of length $n=2^{30}$. Here $d=n/16-1$, $t=n/4-5,100,000$, $s=t/n$ and $R=d/n$. The proof makes interpolation multiplicities depend on the actual site populations of the hypothetical list. [Exact certificate](../../../scripts/probes/probe_sixteenth_list_adaptive_quotient.py)

The [uniform second-interpolant proof](sixteenth-list-quotient-jets.md) defines the local rank $C$, source size $N(w,h)$ and the local order $o_x$ of an irreducible primary factor $g$ of weight $D_g$ and derivative degree $v$. Use primary order 7 and derivative degree cap 2. Its positive surplus is 262,417,820. As in that proof, a macroscopic group on one factor retains more than $M_0=n-1000$ regular distinct words after removing the intersections of $g$ and $g_V$. Choose $t$ hits per retained word. Write $p_x=c_x/M$ for the proportion of the $M$ words selecting site $x$. The same incidence and order arguments give
$$
 \mathbb Ep_x=s,\quad \operatorname{Var}(p_x)\le V_0=R-s^2+(s-R)/M_0,\quad
 \mathbb E(p_xo_x)\le s+(D_g-d+1)/n,\quad 0\le o_x\le D_g/d+v ,
$$
where the expectation is uniform on the $n$ sites.

Take $r=5000$, weight cutoff $w=(r-2)t$, and assign the second interpolant local order
$$
                        q_x=\lfloor r+\lambda(p_x-s)\rfloor .
$$
Averaged over the group, the weighted agreement count is at least $(r-1)t$, since $\sum_x p_x(p_x-s)=n\operatorname{Var}(p_x)\ge0$. For an individual chosen support $S_i$, one has $\sum_{x\in S_i}c_x\le t+(M-1)d$. Thus its weighted agreement count is at most $rt+\lambda nV_0$. At least $Mt/(2t+\lambda nV_0)$ words have weighted agreement count at least $w$. For each parameter row used below this exceeds the product of the two total degrees in $(Y,V)$. A second interpolant of weight below $w$, independent of $g$ and obeying the local quotient conditions, would vanish identically on all these words and violate Bézout.

For a fixed derivative cap $h$ set
$$
 B(q)=C(q,h)-C(q,h-v),\qquad J(q)=C(q,h-v)-C(q-1,h-v).
$$
The local quotient cost is at most $B(q_x)+J(q_x)o_x$. Indeed successive increments of $C(q,h-v)$ are nondecreasing: multiplication by $u=X-x$ embeds one associated graded piece of the local substitution space into the next. Put $b_1=(B(r+10)-B(r-10))/20$ and $L=J(r)/s$. The verifier checks
$$
 \begin{aligned}
 B(q_x)&\le B(r)+b_1\lambda(p_x-s)+r/2+b_2r^2(p_x-s)^2,\\
 J(q_x)&\le Lp_x+r/2+j_2r^2(p_x-s)^2
 \end{aligned}
$$
for every real $0\le p_x\le1$ using the following rational constants.

| $v$ | $h$ | $\lambda$ | $b_2$ | $j_2$ |
|---:|---:|---:|---:|---:|
| 1 | 4400 | 16694 | 4.2 | 1.4 |
| 2 | 1400 | 17537 | 12.4 | 0.4 |

For each possible integer $q_x$ write $a=q_x-r$. Then $p_x-s\ge a/\lambda$ and $(p_x-s)^2\ge\min(|a|,|a+1|)^2/\lambda^2$. The linear coefficients are positive. These substitutions reduce the checks to one exact rational comparison per integer and per row of the two inequalities.

Taking expectations, the total secondary local cost divided by $n$ is at most
$$
 B(r)+r/2+b_2r^2V_0+
 L\big(s+(D_g-d+1)/n\big)+(r/2+j_2r^2V_0)(D_g/d+v).
$$
The source dimension modulo $g$ remains $N(w,h)-N(w-D_g,h-v)$. Its surplus over this cost is concave in $D_g$, so endpoints suffice. At $v=1$ take the endpoints $9n/16-15$ and $7t-1$, obtaining positive surpluses at least 45,411,223,790,778 and 21,834,870,744,462,409. At $v=2$ the endpoints $2(d-1)$ and $7t-1$ give at least 779,874,757,569,825 and 3,324,285,524,980,252. The resulting Bézout contradiction rules out both rows.

Every remaining large group consequently has $v=1$ and weight below $9n/16-15$. The linear-equation count in the uniform proof bounds it by 1,073,741,805. Even twice this number plus the total $(Y,V)$ degree of the primary factorization is below $2n+1$. This proves the stated safety guarantee.
