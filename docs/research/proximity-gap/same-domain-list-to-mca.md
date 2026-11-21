# A same-domain reduction from Reed–Solomon lists to mutual correlated agreement

Let $H\subseteq\mathbb F_q$ have $n$ elements and let $C$ evaluate all degree-$<k$ polynomials on $H$. Fix $1\le k<t\le n$. Suppose a word $y$ agrees with each of $L\ge1$ distinct polynomials in at least $t$ positions. There is one pair of received words on $H$ for which at least

$$
 \left\lceil\frac{L(q+1)}{q+1+(L-1)(k-1)}\right\rceil
$$

distinct folding scalars give a mutual correlated agreement error at radius $(n-t)/n$. An error here means that on some set of at least $t$ sites, the folded word agrees with a codeword while the two received words admit no joint pair of codewords on that set. The set can depend on the folding scalar. The alphabet, individual-word dimension, domain and integer radius in the conclusion equal those in the hypothesis. The statements for a supplied polynomial family and for the worst-center closed-list function are `from_polynomials` and `from_list`. [Lean proof](../../../ArkLib/Research/ProximityGap/Frontier/SameDomainListMca.lean)

## The three received pairs

For a projective point $z$, use the label $-v_z(f)$. At finite points $v_z(f)=f(z)$, and at infinity it is the coefficient of $X^{k-1}$. Once $z$ and $y$ are fixed, the same two words work for every member of the list.

- For $z\in H$, take $u=y$ away from $z$, $u(z)=0$, and $v=-1$ at $z$ and zero elsewhere. If $A_f$ is the original agreement set, $u-f(z)v$ agrees with $f$ on $A_f\cup\{z\}$, including when $z\notin A_f$. A polynomial representing $v$ there would vanish at at least $t-1\ge k$ sites and take value $-1$ at $z$.
- For finite $z\notin H$, take $u(x)=y(x)/(x-z)$ and $v(x)=1/(x-z)$. The folded polynomial is $(f(X)-f(z))/(X-z)$. If a polynomial $b$ of degree $<k$ represented $v$ on the agreement set, $(X-z)b(X)-1$ would have more than $k$ distinct roots and value $-1$ at $z$.
- For $z=\infty$, take $u(x)=x y(x)$ and $v(x)=x^k$. The folded polynomial $Xf(X)-v_\infty(f)X^k$ has degree $<k$. A representative of $v$ would give a nonzero degree-$k$ polynomial $X^k-b(X)$ with at least $t>k$ roots. [Three witnesses](../../../ArkLib/Research/ProximityGap/Frontier/ProjectiveListTransfer.lean)

## Counting labels

Two different list polynomials have the same value at at most $k-1$ projective points. If they agree at infinity their difference has degree $\le k-2$, allowing at most $k-2$ further finite coincidences. For $k=1$, two distinct constants differ at every point, including infinity.

Write $N=q+1$, and let $E_z$ count ordered pairs of list polynomials with equal $z$-values, including the diagonal. Summing first over pairs gives $\sum_z E_z\le L N+L(L-1)(k-1)$. Choose $z$ at which the energy is at most this average. Cauchy–Schwarz on the sizes of the evaluation fibers gives $L^2\le |v_z(\mathrm{list})|E_z$, which proves the stated rounded bound. [Finite counting lemma](../../../ArkLib/Research/ProximityGap/Frontier/FiniteFingerprintCount.lean)

## Security implications and relation to prior reductions

For tolerance $1/Q$, set $B=\lfloor q/Q\rfloor$. If $B^2(k-1)<q+1$, substituting $L=B+1$ in the lower bound gives more than $B$ bad scalars. Consequently MCA error at most $1/Q$ certifies a scalar closed list of size at most $B$ at the same grid point. At $Q=2^{128}$, $k\le2^{40}$, and $q\le2^{216}$, one has $B(k-1)\le2^{128}$ and $B^2(k-1)\le q$. This covers the two originally nominated production primes of budgets $2^{30}$ and $2^{31}$. Determining the worst-case MCA error still requires an independent bound or construction. [Formal tolerance corollaries](../../../ArkLib/Research/ProximityGap/Frontier/SameDomainListMca.lean)

Gao, Yang, Xu and Kan prove an analogous Reed–Solomon reduction with $q$ in place of $q+1$ in the counting expression, allowing a replacement evaluation site. The projective proof above realizes each labeling with a received pair on the original domain, including when the domain already uses all finite field elements. [Gao–Yang–Xu–Kan, Corollary 2](https://arxiv.org/abs/2607.10572)

The earlier DEEP transfer in this repository takes a list in dimension $k+1$ and produces bad scalars in dimension $k$ by counting collisions outside $H$. It can already accept a dimension-$k$ list through inclusion when there are enough external points, including for the two originally nominated production primes. The projective result gives a quantitative bound for arbitrary finite domains and fields and also works when every finite point is in $H$. Earlier work by Crites and Stewart develops DEEP reductions between agreement and list-decoding statements. [Existing DEEP theorem](../../../ArkLib/Research/ProximityGap/Frontier/DeepListMcaTransfer.lean) · [Crites–Stewart](https://eprint.iacr.org/2025/2046) · [Prize problem definitions](https://eprint.iacr.org/2026/680)

## Why a general Möbius repair cannot transport a one-site change

The following auxiliary statement has a written proof. Let $H=\mu_n$ in a field containing all $n$-th roots of unity, with $n\ge6$ and characteristic zero or $p>n+1$. If a Möbius image of $H$ shares at least $n-1$ points with $H$, the image equals $H$.

Scale the input by an element of $H$ so that all points of $H\setminus\{1\}$ have images in $H$. For the transformation $(aX+b)/(cX+d)$ with $ad-bc\ne0$, the polynomial $F=(aX+b)^n-(cX+d)^n$ is divisible by $1+X+\cdots+X^{n-1}$. The quotient has degree at most one, so all coefficients of $X^i$ for $1\le i\le n-1$ have a common value $C$. If $C=0$, then $F=A X^n+B$ and vanishing at one root in $H$ gives vanishing throughout $H$. A pole cannot be a zero of $F$ since numerator and denominator never vanish together. Thus the entire image lies in $H$ and has $n$ points.

If $C\ne0$, the sequence $1/\binom ni=C^{-1}(a^i b^{n-i}-c^i d^{n-i})$ on the interior indices is a sum of at most two geometric sequences. Terms with a zero base vanish on all the interior indices. A linear recurrence $s_{i+2}=u s_{i+1}+v s_i$ therefore holds for some $u,v$. All binomial coefficients are invertible by the characteristic hypothesis. Clearing the ratios of successive binomial coefficients yields

$$
 (i+1)(i+2)=u(i+1)(n-i-1)+v(n-i)(n-i-1).
$$

It holds for $1\le i\le n-3$, hence as a polynomial identity because there are at least three distinct values and the degree is at most two. At $i=n-1$ it gives $n(n+1)=0$, a contradiction. This auxiliary argument explains why projective coordinate changes alone cannot guarantee recovery of the original subgroup after a genuine one-site change. The Lean transfer above uses received-word constructions directly.
