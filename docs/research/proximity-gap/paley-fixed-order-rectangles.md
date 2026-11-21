# Prescribed rectangles for a fixed-order multiplicative character

Let $p$ be prime and let $\chi$ be a multiplicative character of exact order $k\ge2$ on $\mathbb F_p^\times$, extended by $\chi(0)=0$. Set $d=(p-1)/k$ and $c_k=\cos(2\pi/k)$. For prescribed sets $A,B\subseteq\mathbb F_p$ put $a=|A|$, $b=|B|$ and $S_\chi=\sum_{u\in A,v\in B}\chi(u+v)$. Assume $2\le a\le d+1$ and $b\ge1$. For each integer $1\le x\le a/2$, define $R=b^2(a-2x)^2+4bx(d+1-x)$. Then
$$
 |S_\chi|^2\ \le\ \frac{1+c_k}{2}(ab)^2+\frac{1-c_k}{2}R.                 \tag{1}
$$
Reflecting $B$ gives the same bound for differences. The proof also bounds the number of edges of each multiplicative color in the rectangle.

**The color estimate.** Identify the values of $t^d$ on $\mathbb F_p^\times$ with the values of $\chi(t)$ by a group isomorphism. Fix a field-valued color $\eta\in\mu_k(\mathbb F_p)$. For each shift $v$, let $e_v$ count the $u\in A$ with $u+v\ne0$ and $(u+v)^d\ne\eta$. Write $m=a-1$, $D=d+m$, and $c_u=\prod_{w\in A\setminus\{u\}}(u-w)^{-1}$. The interpolation moments give $\sum c_u(X+u)^m=1$ and $\sum c_u(X+u)^j=0$ for $0\le j<m$. Take
$$
 F(X)=\sum_{u\in A}c_u(X+u)^D-\eta,\qquad
 G_v(X)=\sum_{u\ {\rm counted\ by}\ e_v}
         c_u\bigl(1-\eta/(u+v)^d\bigr)(X+u)^D .
$$
For $0\le j<m$, the $j$th derivative of $F-G_v$ at $v$ is
$[D]_j\eta\sum c_u(u+v)^{m-j}-\eta\mathbf1_{j=0}=0$, where $[D]_j$ is a falling factorial. A zero site contributes zero since both powers there have positive exponent. Thus $(X-v)^m\mid F-G_v$, with $G_v$ supported on $e_v$ powers. The choice of coefficient works for every nonzero field color. Hanson and Petridis use the barycentric polynomial to handle perfect multiplicative-subgroup containment. [Hanson and Petridis, Theorem 1.2](https://arxiv.org/abs/1905.09134)

The first surviving coefficient of $F$ is $\binom Dm\ne0$ at degree $d$. For $h=x-1$ the determinant of $(F^{(i+j)}/[D]_{i+j})_{0\le i,j\le h}$ has degree $x(d+1-x)$. The degree lemma applies because $D\le2d<p$, $2h\le d$, and $h\le m$. The local determinant lemma applies to the contact just proved and gives order at least $r(m-2h+r-1)$ at $v$ for $r=(x-e_v)_+$. This equals $(x-e_v)_+(a-x-e_v)_+$. Summing over $B$ bounds the total charge by $x(d+1-x)$. [Degree lemma](../../../ArkLib/Research/ProximityGap/Frontier/PaleyHankelDegree.lean) · [Local determinant lemma](../../../ArkLib/Research/ProximityGap/Frontier/PaleyDefectMinor.lean)

Let $E_\eta$ count all entries of color $\eta$ and let $z$ count zero entries. On each row $a-2e_v\le a-2x+2(x-e_v)_+$. The right side is nonnegative and its square equals $(a-2x)^2+4(x-e_v)_+(a-x-e_v)_+$. Cauchy–Schwarz and the total charge bound give $2E_\eta-ab+2z\le\sqrt R$. [Finite Cauchy inequality](../../../ArkLib/Research/ProximityGap/Frontier/PaleyDefectDiscrepancy.lean)

**From color counts to the complex sum.** When $R\ge(ab)^2$, the triangle inequality gives (1). Otherwise put $\mu=(1+\sqrt R/(ab))/2\in[1/2,1)$. Distribute the zero mass equally among all colors, setting $q_\eta=(E_\eta+z/k)/(ab)$. Then $\sum q_\eta=1$, every $q_\eta\le\mu$, and their complex weighted sum remains $S_\chi/(ab)$ because the $k$th roots sum to zero. Under this cap $\sum q_\eta^2\le\mu^2+(1-\mu)^2$. Indeed, moving mass from the smaller of two positive unsaturated coordinates to the larger increases the sum of squares until one is zero or capped. Distinct roots have real inner product at most $c_k$. Expansion gives
$$
 |S_\chi/(ab)|^2\le c_k+(1-c_k)\sum q_\eta^2
 \le 1-2(1-c_k)\mu(1-\mu),
$$
which is (1).

**Square-root scale.** Suppose $k$ is fixed, $a,b\to\infty$, $a\le d+1$, and $d/(ab)\to\lambda\in(0,1)$. Choosing $x/a\to(1-\lambda)/2$ makes $R/(ab)^2\to2\lambda-\lambda^2$. Hence
$$
 \limsup |S_\chi|/(ab)\ \le\
 \sqrt{1-\tfrac12(1-c_k)(1-\lambda)^2}<1.
$$
When $a,b\sim\sqrt p$, one has $\lambda=1/k$. In particular the quadratic constant is $\sqrt3/2$, and the cubic constant is $\sqrt{2/3}$. The estimate gives a fixed saving at this scale. A power saving for arbitrary smaller prescribed sets remains open. [Quadratic sequence theorem](../../../ArkLib/Research/ProximityGap/Frontier/PaleyBalancedLimit.lean)

The higher-order specialization above is a written proof. Run `python3 -O scripts/probes/probe_paley_fixed_order_rectangles.py` for an exact arithmetic check of the cubic and quartic cases at $p=13$. Two coordinate sets and every nonempty $B$ give 273 local multiplicity checks and 49,146 rectangle/parameter tests. [Executable check](../../../scripts/probes/probe_paley_fixed_order_rectangles.py)
