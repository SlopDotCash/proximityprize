# Signed Paley rectangles and a four-site rank bound

Let $p$ run through odd primes and let $A,B\subseteq\mathbb F_p$ have sizes $a,b=(1+o(1))\sqrt p$. Give every site an arbitrary sign $w_u$ or $v_t$. With $\chi(0)=0$,
\[
 \left|\sum_{u\in A,t\in B}w_uv_t\chi(u-t)\right|
 \le (\sqrt3/2+o(1))ab.
\]
The signs can depend on the sets and on each other. The bound extends to arbitrary real vertex weights in $[-1,1]$ by multilinearity. For every $X$ of size $n=(1+o(1))\sqrt p$ at primes $p\equiv1\pmod4$, at most $13/16+o(1)$ of its four-subsets have a singular ternary Paley minor. The rank criterion for the full conjecture asks for a density of $1/4+O(p^{-\eta})$. The proof below gives a uniform signed extension of the existing unweighted constant. [Unweighted rectangle bound](paley-defective-rectangle.md) · [Four-site rank criterion](paley-four-site-rank.md)

## Finite row estimate

Write $d=(p-1)/2$, assume $2\le a\le d+1$, and choose $1\le x\le\lfloor a/2\rfloor$. Put
\[
 W_w(t)=\sum_{u\in A}w_u\chi(t+u),\qquad z_t=\mathbf1_{-t\in A},\qquad
 s=\min\big(\#\{u:w_u=1\},\#\{u:w_u=-1\}\big).
\]
For $y_+=\max(y,0)$ define
\[
 D_x=x(d+a-2x)-(x-s)_+(a-x-s)_+.
\]
Then
\[
 \sum_{t\in\mathbb F_p}\big(W_w(t)^2-(a-z_t-2x)^2\big)_+\le 4D_x. \tag{1}
\]
Consequently any prescribed $B$ satisfies
\[
 \sum_{t\in B} W_w(t)^2\le
 \sum_{t\in B}(a-z_t-2x)^2+4D_x.
\]
Cauchy–Schwarz bounds $\left|\sum_{t\in B}v_tW_w(t)\right|^2$ by $b$ times this right side. Taking $x/a\to1/4$ when $a,b\sim\sqrt p$ gives $3/4+o(1)$ after division by $a^2b^2$. Reflection gives the difference convention. More generally, if $a,b\to\infty$ and $d/(ab)\to\lambda\in(0,1)$, taking $x/a\to(1-\lambda)/2$ bounds the normalized squared row mass by $2\lambda-\lambda^2+o(1)$.

## The determinant survives arbitrary signs

Set $h=x-1$, $D=d+a-2<p$ and $c_u=\prod_{v\in A\setminus\{u\}}(u-v)^{-1}$. The Lagrange leading-coefficient functional gives $\sum_u c_u u^j=0$ for $0\le j<a-1$ and $1$ for $j=a-1$. Form
\[
 F(X)=\sum_u c_uw_u(X+u)^D,\qquad
 J_{ij}=\frac{F^{(i+j)}}{[D]_{i+j}}
       =\sum_u c_uw_u(X+u)^{D-i-j},\qquad 0\le i,j\le h ,
\]
where $[D]_k$ is a falling factorial. All normalizers are units. The signed-factor polynomials in the earlier factorization vary one global sign. Here $w_u$ changes the coefficient at each individual site. Its effect on degree requires a separate argument. [Earlier global-sign factorization](paley-shift-multiplicities.md#two-determinants-recover-the-sign)

Put $N=D-h$. Then $a-1\le N<p$. Reverse the columns of $J$ so that column $k$ uses $(X+u)^k$ times the common row factor $(X+u)^{N-i}$. Replacing $(X+u)^k$ by $u^k=((X+u)-X)^k$ uses a triangular matrix over $\mathbb F_p[X]$ with diagonal one. Thus, up to the reversal sign, the new determinant is
\[
 \det\left( \frac{f_j^{(i)}}{[N]_i}\right)_{0\le i,j<x},\qquad
 f_j=\sum_u c_uw_u u^j(X+u)^N .
\]
For each fixed $j$, the stated matrix entry follows by differentiating the displayed $f_j$. The change of columns took place on the already formed matrix, so no derivatives of the triangular coefficients occur.

The $a$ shifted powers $(X+u)^N$ are linearly independent. Their coefficients at $X^{N-k}$ for $0\le k<a$ give a Vandermonde matrix times the nonzero diagonal $\binom Nk$. Each $c_uw_u$ is nonzero. Therefore the map $P\mapsto f_P=\sum_u c_uw_u P(u)(X+u)^N$ is injective on the polynomials of degree less than $x$. The $x$ polynomials have a basis with distinct degrees $0\le l_0<\cdots<l_{x-1}\le N<p$. The Wronskian has a nonzero coefficient at degree $\sum_j l_j-\binom x2$. Indeed the determinant of the leading coefficients, after removing nonzero scalars, is the falling-factorial Vandermonde $\det([l_j]_i)=\prod_{j<k}(l_k-l_j)$. This proves $\det J\ne0$ in characteristic $p$ and gives $\deg\det J\le x(N-x+1)=x(d+a-2x)$.

For the sharper degree choose a minority-sign set $M$ of size $s$. If $s<x$, take monic polynomials $P_j(U)=U^{j-s}\prod_{u\in M}(U-u)$ of degrees $s\le j<x$. We have $w_uP_j(u)=\sigma P_j(u)$ for one fixed sign $\sigma$. The first nonzero moment $\sum_u c_u w_u P_j(u)u^k$ is at $k=a-1-j$ and equals $\sigma$. Hence $f_{P_j}$ has degree $N-a+1+j$. A complementary $s$-dimensional space has a basis with degrees at most $N,N-1,\ldots,N-s+1$ in descending order. Compared with the top $x$ degrees $N,N-1,\ldots,N-x+1$, this loses $(x-s)(a-x-s)$ from their sum. Thus $\deg\det J\le D_x$ in all cases. In fact equality holds for $s\le x$. For $s>0$ the first $s$ high-degree coefficients, indexed by $0\le k<s$, are nonzero binomial multiples of $-2\sigma\sum_{u\in M}c_u P(u)u^k$, since $\deg(P(U)U^k)\le x+s-2<a-1$. Evaluation onto $M$ and its Vandermonde matrix have full rank $s$. This realizes the top $s$ pivot degrees, distinct from all the listed degrees of the $f_{P_j}$. The case $s=0$ already has its full basis.

## Local order and the central factorization

Fix $t$. Let $\tau$ be a majority nonzero sign among $w_u\chi(t+u)$, let $E_t$ be the sites with the opposite sign, and put $e_t=|E_t|=(a-z_t-|W_w(t)|)/2$. Set $G_t=2\sum_{u\in E_t} c_u w_u(X+u)^D$ and $\nu=a-1-z_t$. For $0\le j<\nu$ the normalized $j$th derivative of $F-G_t$ at $t$ equals $\tau\sum_u c_u(t+u)^{a-2-j}=0$. At nonzero sites this follows from Euler's criterion. At a zero site both exponents are positive in this range. Taylor expansion is valid since $D<p$, so $(X-t)^\nu$ divides $F-G_t$.

The normalized jet matrix of $G_t$ is a sum of $e_t$ rank-one matrices over $\mathbb F_p(X)$. Each residual entry in position $(i,j)$ vanishes to order at least $\nu-i-j$. In a size-$k$ minor the row and column indices are distinct, so the minimum order is at least $k(\nu-2h+k-1)$. The complementary-minor expansion forces $k\ge x-e_t$, and $\nu\ge2h$. If $e_t<x$, the determinant therefore vanishes to order at least $(x-e_t)(a-z_t-x-e_t)$. Four times this product equals $W_w(t)^2-(a-z_t-2x)^2$. When $e_t\ge x$ the positive part of this difference is zero because $0\le a-z_t-2e_t\le a-z_t-2x$. Summing the local inequalities and using the degree bound proves (1). [Complementary-minor order lemma](../../../ArkLib/Research/ProximityGap/Frontier/PaleyDefectMinor.lean)

At $x=\lfloor a/2\rfloor$, the square $(a-z_t-2x)^2$ is zero for even $W_w(t)$ and one for odd $W_w(t)$. Thus the local bound is $\operatorname{ord}_t\det J\ge\lfloor W_w(t)^2/4\rfloor$. Shift orthogonality gives $\sum_t W_w(t)^2=pa-(a-2s)^2$. There are $a$ odd rows for even $a$ and $p-a$ odd rows for odd $a$. Subtracting the odd-row count and dividing by four gives $x d-(x-s)^2$ when $a=2x$, and $x(d+1)-(x-s)(x+1-s)$ when $a=2x+1$. These are precisely $D_x$ in the two cases. Every unit of degree has therefore been accounted for, giving the polynomial identity
\[
 \det J=\operatorname{lc}(\det J)\prod_{t\in\mathbb F_p}(X-t)^{\lfloor W_w(t)^2/4\rfloor}.
\]
This includes degree zero and the endpoint $p=3,a=2,x=1$.

The original pair reconstruction persists with the site signs. For $u\ne v$ let $Q_{uv}$ be the monic normalization of $w_u(X+u)^d-w_v(X+v)^d$. Its roots are exactly the shifts giving equal nonzero signed symbols at $u,v$, all simple. Indeed $(X+u)/(X+v)$ bijects the affine line minus $-v$ with the affine line minus $1$, and the roots of $Y^d=w_v/w_u$ are nonzero and simple. There are $d-1$ such finite shifts for equal signs and $d$ for opposite signs, exactly the degree in each case. At a fixed shift with $j$ positive and $k$ negative signed symbols, the product over pairs therefore has order $\binom j2+\binom k2$. Subtracting $\lfloor(j-k)^2/4\rfloor$ leaves $c_{j+k}=\lfloor(j+k)/2\rfloor\lfloor(j+k-1)/2\rfloor$. This gives the monic identity
\[
 \prod_{\{u,v\}\subset A}Q_{uv}(X)
   =\frac{\det J}{\operatorname{lc}(\det J)}
     \prod_{t\in\mathbb F_p}(X-t)^{c_{a-z_t}}
 \qquad (x=\lfloor a/2\rfloor).
\]

## What the four-site count gives in each prime class

Let $3\le n=|X|\le d+2$. For each $t\in X$ use source $A=X\setminus\{t\}$ and signs $w_u=\chi(u-t)$. On the reflected targets $-b$ for $b\in X$, the resulting rows are exactly $G(t,b)=\sum_{u\in X}\chi(u-t)\chi(u-b)$. Among the $n$ targets, $n-1$ have a zero source entry and one has none. Dropping the minority correction in $D_x$ and summing (1) gives the explicit ceiling
\[
 E=\sum_{t,b\in X}G(t,b)^2\le U_x
 =n\left[(n-1)(n-2-2x)^2+(n-1-2x)^2+4x(d+n-1-2x)\right],\quad
 1\le x\le\lfloor(n-1)/2\rfloor .
\]
The diagonal terms give $E\ge L=n(n-1)^2$. Write $R=n(n-1)(2n-3)$, $C=\binom n4$ and $N_4$ for the number of singular four-subsets modulo three. The exact identity $E=R+8\chi(-1)(4N_4-C)$ yields the following integer bounds, also clipped to $[0,C]$. [Four-site normalization](paley-four-site-rank.md#exact-normalization-and-the-four-site-determinant)

| Prime class | Lower bound for $N_4$ | Upper bound for $N_4$ |
| --- | --- | --- |
| $p\equiv1\pmod4$ | $\lceil C/4+(L-R)/32\rceil$ | $\lfloor C/4+(U_x-R)/32\rfloor$ |
| $p\equiv3\pmod4$ | $\lceil C/4-(U_x-R)/32\rceil$ | $\lfloor C/4-(L-R)/32\rfloor$ |

If $n\sim\sqrt p$, take $x/n\to1/4$ to obtain $E/n^4\le3/4+o(1)$. For $p\equiv1\pmod4$ this gives $N_4/C\le13/16+o(1)$. For $p\equiv3\pmod4$, the lower estimate at this scale is weaker than $N_4\ge0$, and the upper estimate is $1/4+O(1/n)$. More generally at $n^2/p\to\beta>1/2$ the normalized energy ceiling is $g(\beta)=1/\beta-1/(4\beta^2)$. In the latter prime class it yields a positive asymptotic lower density $(1-3g(\beta))/4$ when $\beta>(3+\sqrt6)/2$. As a finite check, at $p=3,n=3,x=1$ the upper bound for $E$ is $18$, the actual energy. At $p=65537$, every 256-site set satisfies $E\le3{,}196{,}058{,}880$ with $x=63$, so at most 142,536,640 of its 174,792,640 four-subsets are singular. For any two prescribed 256-site sets and any vertex signs, $x=64$ gives an absolute discrepancy of at most 56,829 out of 65,536.

## Additive energy in every chart of a near-extremizer

Suppose $a,b\sim\sqrt p$ and put $c_0=\sqrt3/2$. If the signed discrepancy divided by $ab$ tends in absolute value to $c_0$, then the additive energy of **each side in every common projective chart** is $o(p^{3/2})$, uniformly over the charts. Here $E_+(Y)=\#\{y_1+y_2=y_3+y_4 : y_i\in Y\}$ for the finite image $Y$, after dropping its possible point at infinity. More quantitatively, if one side in some chart satisfies $E_+(Y)\ge\kappa|Y|^3$ along a sequence of primes with fixed $0<\kappa\le2/3$, then
\[
 \limsup\frac{|S|}{ab}\le\Phi\!\left((3\kappa/2)^{1/3}\right),\qquad
 \Phi(\alpha)=
 \begin{cases}
    \sqrt{3/4-\alpha},&0\le\alpha\le1/2,\\
    1-\alpha,&1/2\le\alpha\le1 .
 \end{cases}
\]
The sets, signs and chart may vary at each prime. The factorization of a projective difference changes only the two vertex signs and a global sign. Dropping a pole costs at most $a+b=o(ab)$. [Projective sign transformation](paley-four-site-rank.md#the-signed-four-cycle-controls-a-prescribed-rectangle)

To see how a structured piece contributes, let $Z$ denote the other image and $T\subseteq Y$ have $|T|\gg\sqrt p$ and $|T+T|\le K|T|$ for fixed $K$. Chang's theorem gives a power saving for all unweighted cuts on at least half of $T$ and half of $Z$. Indeed their sizes exceed $p^{4/9+1/36}$ for large $p$ and every such half of $T$ has doubling at most $2K$. Reflection preserves doubling. The dense-cut transfer then gives $o(ab)$ on $T\times Z$ uniformly over both sign functions. This also applies to the union $U$ of any bounded number of disjoint such pieces. If $|U|/|Y|\to\alpha$, Cauchy–Schwarz on $Y\setminus U$ and (1) for the original row squares give the coefficient $c_0\sqrt{1-\alpha}$. Applying (1) afresh to the remaining rectangle does better. Its product of sizes divided by $p$ tends to $1-\alpha$. For $\alpha<1/2$, substituting $\lambda=1/[2(1-\alpha)]$ in the finite row estimate and multiplying by the remaining relative area gives $\sqrt{3/4-\alpha}$. For $\alpha\ge1/2$ use the remaining area itself. [Chang, Theorem 6](https://math.ucr.edu/~mcc/paper/132%20DL.pdf) · [Dense-cut transfer for arbitrary signs](paley-projective-doubling.md#dense-subsets-suffice-despite-arbitrary-vertex-signs)

Write $m=|Y|$ and fix $\rho>0$. While the remaining set $R$ has $E_+(R)>\rho m^3$, we have $|R|>\rho^{1/3}m$ and $E_+(R)>\rho|R|^3$. The Balog–Szemerédi–Gowers theorem supplies a subset of size $\gg_\rho m$ with bounded difference constant, hence bounded doubling by the sum–difference inequality. Remove it. After $O_\rho(1)$ iterations the removed set $U$ is a union as above and $E_+(R)\le\rho m^3$. By Fourier inversion, $E_+(Y)^{1/4}$ is the normalized Fourier $L^4$ norm of $\mathbf1_Y$, so Minkowski gives $E_+(Y)^{1/4}\le E_+(U)^{1/4}+E_+(R)^{1/4}$. [Reiher and Schoen, sum-energy form of Balog–Szemerédi–Gowers](https://arxiv.org/abs/2308.10245)

For $u=|U|$ we have $2u\le p$ eventually. If $r(z)$ counts differences in $U^2$, Pollard's theorem gives $\sum_z(r(z)-t)_+\le(u-t)^2$ for $1\le t<u$. Thus $E_+(U)\le u^2+2\sum_{t=1}^{u-1}(u-t)^2=(2u^3+u)/3$. Minkowski now gives $\kappa^{1/4}\le(2/3)^{1/4}(u/m)^{3/4}+\rho^{1/4}+o(1)$. First pass to the large-prime limit at fixed $\rho$, then let $\rho\downarrow0$ and use continuity and monotonicity of $\Phi$. Every fixed $\kappa>0$ gives a strict improvement on $c_0$, proving the assertion about near-extremizers. The energy argument leaves unrestricted the case of two sets with small normalized energy in every chart. [Pollard's theorem for sums of residue classes](https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/jlms/s2-8.3.460)

## Overlap in the skew prime class

Suppose $p\equiv3\pmod4$, $|A|=|B|=m\sim\sqrt p$ and $|A\cap B|/m\to\theta$. For the ordinary difference sum, if $1-c_0<\theta<1$ then
\[
 \limsup\frac{|S(A,B)|}{m^2}\le
 \min\!\left\{1-\theta^2,\;
 \theta(1-\theta)+\sqrt{(1-\theta)\bigl(3/4-\theta(1-\theta)^2\bigr)}\right\}<c_0 .
\]
At $\theta=1$ the relative discrepancy tends to zero. Consequently a sequence reaching $c_0$ must have overlap at most $(1-c_0+o(1))m$.

Indeed the sum on $C\times C$ for $C=A\cap B$ vanishes by skew symmetry, giving the first bound. Orient all row sums to make their total nonnegative. Let $u,v$ be their respective averages on $C$ and $B\setminus C$, each divided by $m$. Then $|u|\le 1-|C|/m$, again by skew symmetry. By (1) and Cauchy–Schwarz the limiting constraints give $\theta u^2+(1-\theta)v^2\le c_0^2$. At fixed $u$, the largest possible mean is $\theta u+\sqrt{(1-\theta)(c_0^2-\theta u^2)}$. It increases up to $u=c_0$, so $u\le1-\theta<c_0$ gives the second bound. The argument also applies to vertex signs whose restrictions to $C$ agree up to a single global sign. For disjoint sides this overlap argument allows the original constant.

## Reproduction

Run `python3 -B scripts/probes/probe_paley_signed_square_root.py`. At $p=3,5,7,11,13$ the program checks all signed source subsets of the admissible sizes up to simultaneous sign reversal, all widths $x$, and the worst target set through the positive part in (1). It checks 614,126 row budgets, computes 1,300 polynomial determinants and their local orders directly, verifies 716 signed pair-product identities, and compares 8,863 principal Gram energies with integer determinants of the four-site minors. The signed Wronskian argument and its consequences are proved above and checked by this finite probe. [Exact verifier](../../../scripts/probes/probe_paley_signed_square_root.py)
