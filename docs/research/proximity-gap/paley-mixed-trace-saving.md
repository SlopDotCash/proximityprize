# A power saving for every distinct pair of product strata

Let $H=\langle g\rangle\subseteq\mathbb F_p^\times$ have order $n$ divisible by
four. For $s\in H$ put $T(s)=\{x+s/x:x\in H\}$, and let $S$ be the ordered
quadratic-character difference sum on $T(s)\times T(t)$ for $s\ne t$. Uniformly
over the specified two products, for $n\ge4p^{1/4}$ one has
$$
\frac{|S|}{|T(s)||T(t)|}
\ll \frac{p^{1/8}}{n^{1/3}}+p^{-1/8}+n^{-1}.
$$
Consequently every fixed pair of different strata has a relative power saving
when $n\ge p^{3/8+\epsilon}$. In the Goldilocks field $p=2^{64}-2^{32}+1$,
on the subgroup of order $2^{30}$, the relative sum is **strictly below
$4/5$** on every such pair. Both sets have size about one eighth of $\sqrt p$.
The two larger designated prize primes have $n$ below the power-saving range
of the general estimate. [Finite Lean components](../../../ArkLib/Research/ProximityGap/Frontier/PaleyMixedTraceSaving.lean)

## Passing to two subgroup variables

Write $x=g^i$, $y=g^j$, $u=x/y$, $v=xy$, and $\epsilon=\chi(g)$. Then
$$
x\big[(x+s/x)-(y+t/y)\big]=(u-1)v-tu+s .
$$
The complete multiset sum $D$ weights the character of this right side by
$\epsilon^i$. The exponent indices of $u,v$ have the same parity, and each
such pair has two preimages. If their indices modulo four are $a,b$, then
$\epsilon^i=\epsilon^{(a+b)/2}$, since $4\mid n$. Thus $D$ is twice a
signed sum of eight rectangles on cosets of $K=H^4$, of size $m=n/4$.
When $\epsilon=1$ only two rectangles are needed, on cosets of $K=H^2$,
of size $m=n/2$. [Two-to-one cyclic sum theorem](../../../ArkLib/Research/ProximityGap/Frontier/PaleyInversionTrace.lean)

In any one rectangle write $u=\alpha X$, $v=\beta Y$ with $X,Y\in K$.
Remove the at most two source values $X=1/\alpha,s/(t\alpha)$.
With $a=s/(t\alpha)$, $b=1/\alpha$, and $c=t/\beta$, the remaining kernel is
$$
\chi((1-\alpha X)\beta)\,\chi(f(X)-Y),\qquad
f(X)=c\frac{X-a}{X-b}.
$$
Since $a,b,c$ are nonzero and $a\ne b$, $f$ is injective on its regular
domain. Thus its sign factor gives fixed row weights of modulus one.

## Occupancy and the fourth moment

For each multiplicative coset $wK$, let $L_w$ count its elements in the
regular image of $f$. A point contributing to $L_w$ satisfies $X^m=1$ and
$(f(X)/w)^m=1$. For nonzero $w$, the two rational functions $X^m$ and
$(f(X)/w)^m$ on the projective line have disjoint zero and pole supports
$\{0,\infty\}$ and $\{a,b\}$. They are multiplicatively independent modulo
constants, each has degree $m$ and nonzero differential since $m\mid p-1$,
and the Euler characteristic in the theorem of Corvaja and Zannier is two.
Their positive-characteristic gcd bound gives
$$
L_w\le L=\max\{(108m^2)^{1/3},12m^2/p\}.
$$
The regular image omits zero. The elementary Stepanov theorem in the
repository also gives the separate integral bound
$$
L_w\le\left\lfloor\frac{2j^2-1+m(j-1)+m(2j-1)}{j^2}\right\rfloor
$$
whenever $j\ge1$, $2j^3\le m$ and $2j^2-1+m(j-1)<p$. This finite version
is proved in Lean directly for the fractional-linear image.
[Corvaja–Zannier, Theorem 2](https://doi.org/10.4171/JEMS/409) ·
[Finite Stepanov argument](../../../ArkLib/Research/ProximityGap/Frontier/MobiusSubgroupBound.lean)

Let $R$ be the signed sum on the regular part of one rectangle and let
$r=\lfloor p^{1/4}\rfloor$. Sample any $r$ elements of $K$. Subgroup
amplification recovers each complete row as a sum of dilated sample rows.
The fixed signs multiply these rows and disappear on taking fourth powers.
The product sites have multiplicity at most $L$. Applying Hölder and the
repository's fourth moment on the sampled shifts gives
$$
r^2 |R|^4\le (m^2)^3 C(p)Lp,\qquad C(p)\le17.
$$
This signed version is proved in Lean. Since $r\ge p^{1/4}/2$,
the relative bound on a regular rectangle is
$(4C(p)L\sqrt p/m^2)^{1/4}$. The rectangles exactly exhaust the ratio
and product coordinates after restoring the two exceptional source rows,
whose total cost is at most $2n$ in $D$. [Signed subgroup moment](../../../ArkLib/Research/ProximityGap/Frontier/PaleySubgroupTransversal.lean)

The multiplicity of $x+s/x$ is two except at the at most two fixed points
$x^2=s$, where it is one. The ordinary indicator of its image is half the
sum of its multiplicity function and the indicator of its fixed images.
Thus $|4S-D|\le4n+4$. Dividing by $4|T(s)||T(t)|\ge n^2$ and inserting the
occupancy estimate gives the stated uniform bound.

## The Goldilocks field

Here $7$ is a primitive root. The Lean Lucas proof tests its full power and
the six prime divisors of $p-1=2^{32}\cdot3\cdot5\cdot17\cdot257\cdot65537$.
The subgroup of order $n=2^{30}$ consists of squares, since its index is a
multiple of four. Both parity rectangles therefore have $m=2^{29}$ points
per side. Take $j=645$ in the integral Stepanov bound, giving $L_w\le2494495$.
The choice $r=65535$ satisfies $r^4\le p$, and $C(p)=11$.

For every regular signed parity rectangle, the integer fourth moment gives
$|R|\le230497831808523881$. Restoring the two possible exceptional rows in
that rectangle gives $|R_{\rm full}|\le230497832882265705$.
Lean checks these inequalities, the primality certificate, the rational
substitution and both exceptional rows for every $s,t\ne0$, $s\ne t$.
Consequently $|D|\le4\cdot230497832882265705$. Returning to ordinary sets,
$$
5\big(4\cdot230497832882265705+4n+4\big)<4n^2\le16|T(s)||T(t)|.
$$
This proves $5|S|<4|T(s)||T(t)|$. The numerical statement concerns mixed
products. When $s=t$ the rational map degenerates and the two-thirds
occupancy estimate does not apply.
