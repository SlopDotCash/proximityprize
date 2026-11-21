# The divisible case at the unique-decoding endpoint

Let the domain have $n=k+2e$ sites with $k,e\ge1$ and suppose $e+1$ divides $n+1$. Put $m=(n+1)/(e+1)$ and $s=m-1$. The exact largest scalar MCA numerator over arbitrary evaluation domains, attained over every sufficiently large splitting prime field, is
$$
s(e+1)+1=n-e+1.
$$
The proof below uses the normalized locator and section from the [unique-range proof](apolar-unique-range-all-rates.md). The locator coefficient span, weak coordinate-degree interpolation, negative parameter-degree obstruction and deleted-site lower construction each have kernel-checked Lean proofs. Their final composition is under verification.

## Why the locator spans its full parameter degree

Work over an algebraic closure of the alphabet and write $T$ for the parameter, $X$ for the coordinate. For a bad family of size $M>e+1$, let $f(T,X)$ be the primitive minimal locator, of bidegree $(l,r)$ with $1\le r\le e$ and $1\le l\le r$. The syndrome has degree $d=2e-1$ and is affine in $T$. The generic kernel of the degree-$r$ catalecticant over $K(T)$ has dimension one. Indeed, if a second element exists, cancel its $X^r$ coefficient with that of $f$ to obtain a nonzero $q$ of degree at most $r-1$ with $\lambda(X^j q)=0$ for $0\le j\le d-r$. Since $d\ge2r-1$, apply the recurrence supplied by $f$ to $X^{d-2r+1}q$. Its leading coefficient is nonzero and the lower moments vanish, so $\lambda(X^{d-r+1}q)=0$ as well. This contradicts minimality over the fraction field. The necessary transfer of minimality is explained in the [generic coprimality proof](../../../ArkLib/Research/ProximityGap/Frontier/ApolarGenericCoprime.lean).

Write $f=\sum_{j=0}^l T^jv_j(X)$, and let $U$ be the span of the $v_j$ in the $(r+1)$-dimensional space of coordinate polynomials. Put $b=\dim U$. Restricting the original affine catalecticant to $U$ gives a pencil with $b$ columns and generic rank $b-1$, since its restricted kernel still contains $f$ and is contained in the one-dimensional unrestricted kernel. Select $b-1$ independent rows. Their signed maximal minors give a nonzero polynomial vector in $U[T]$ of parameter degree at most $b-1$ spanning that kernel. As $f$ is primitive, this vector is a polynomial multiple of $f$. Hence $l\le b-1$. There are only $l+1$ vectors $v_j$, so $b=l+1$. Equivalently, the $r+1$ coordinate coefficients of the homogeneous locator span the entire space of binary forms of degree $l$ on the parameter line.

The Lean proof gives an alternative that avoids choosing a minor. If a linear relation on the $v_j$ existed, let $H(T)$ have the reversed coefficients of that relation. The degree-$l$ coefficient of $Hf$ vanishes. Since the moment matrix is affine, its lower part through degree $l-1$ is another kernel vector. For any competing locator $q$ of coordinate degree at most $r$, the divided-polynomial identity $qW_f=fW_q$ and generic coprimality imply $f$ divides $q$. Thus a nonzero kernel vector cannot have parameter degree below $l$. The vanishing lower part forces $T^{l+1}$ to divide every coefficient of $Hf$. At least one coefficient of $f$ is nonzero at zero, so $T^{l+1}$ divides $H$, contradicting $\deg H\le l$. [Affine-kernel proof](../../../ArkLib/Research/ProximityGap/Frontier/ApolarAffineKernelSpan.lean) · [Apolar specialization](../../../ArkLib/Research/ProximityGap/Frontier/ApolarCoefficientSpan.lean)

## The first nonzero coordinate degree

Let $D\subset\mathbb P^1_T\times\mathbb P^1_X$ be the locator divisor, and let $\pi:D\to\mathbb P^1_T$ be projection. Its relative degree is $r$. The primitive locator has no zero fiber. The exact hypersurface sequence in coordinate degree $r$ therefore gives
$$
0\longrightarrow \mathcal O(-l)\longrightarrow
\mathcal O^{r+1}\longrightarrow \pi_*\mathcal O_D(0,r)\longrightarrow0.
$$
The dual of its first map is given by the $r+1$ coefficients of $f$. By the preceding calculation a constant change of basis turns this into the complete evaluation map on the degree-$l$ monomials together with $r-l$ zero columns. The kernel of the complete evaluation map $\mathcal O^{l+1}\to\mathcal O(l)$ is $\mathcal O(-1)^l$: the consecutive monomials give the $l$ syzygies $T_1e_j-T_0e_{j+1}$, which are independent at each point. Dualizing back gives
$$
\pi_*\mathcal O_D(0,r)=\mathcal O(1)^l\oplus\mathcal O^{r-l}.
$$
The argument uses the defining equation and remains valid for reducible or nonreduced locators. Consequently $H^0(D,\mathcal O_D(a,r))=0$ for $a\le-2$.

At power $s$, the coordinate degree of the interpolated section is $b=n-s(d+2-r)$. The identities $n=m(e+1)-1$ and $d=2e-1$ give $b-r=-(m-2)(e-r)\le0$. In the strict case the usual negative-parameter vanishing applies. In the equality case the new splitting gives vanishing whenever the parameter degree $s(l+1)-M$ is at most $-2$. The nonzero section furnished by the bad fibers must therefore have $M\le s(l+1)+1\le s(e+1)+1$. The fixed and proportional syndrome branches contribute at most $e+1$.

For a polynomial version of the equality argument, the two chart remainders have coordinate degree at most $r$. Their cleared difference, divisible by the locator, is $fP(T)$ with $P$ independent of the coordinate. If $a=M-s(l+1)\ge2$, all parameter coefficients of this difference of degrees $l,\ldots,l-2+a$ vanish. The coordinate coefficients of $f$ span all powers $1,T,\ldots,T^l$, so all coefficients of $P$ in degrees $0,\ldots,l-2+a$ vanish. Its degree is at most $l-2+a$ by comparing the parameter degrees on the two sides. Thus the difference vanishes and disjoint exponent ranges force the remainders to vanish. The ordinary fixed-target contradiction completes the proof.

## A domain attaining the count

Take $s$ complete nonzero fibers of $x\mapsto x^{e+1}$ and $e$ sites of a further fiber, omitting one coordinate $t_0$ from that last fiber. They occupy exactly $s(e+1)+e=n$ sites. For a full-fiber label $t$, the lower construction requires only the $e$ sites in the fiber other than $t$. The same identity holds for $t=t_0$, whose whole erased fiber is present. In both cases, for $V$ the domain vanisher and $Q$ the vanisher outside these $e$ sites,
$$
V(X)(X-t)=Q(X)(X^{e+1}-t^{e+1}).
$$
The [power-fiber received pair](../../../ArkLib/Research/ProximityGap/Frontier/PowerFiberEndpoint.lean) gives all $s(e+1)$ complete-fiber labels and the additional distinct label $t_0$. A prime $p>n$ with $p\equiv1\pmod{e+1}$ has enough nonzero fibers: $p-1$ is a multiple of $e+1$ strictly greater than $n-1$, so it is at least $n+1$. These primes may be arbitrarily large.
