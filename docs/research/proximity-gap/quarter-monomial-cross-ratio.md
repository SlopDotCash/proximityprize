# Three-head scores from cross ratios of monomials on the first-prime subgroup

Let $H=\mu_n$ at the first designated prime, $n=2^{30}$. Take four different scaled Laurent monomials $T_i(X)=c_iX^{a_i}$, with arbitrary nonzero scalars over the algebraic closure and arbitrary integer exponents. Consider the rational function
$$
 R=\frac{(T_0-T_1)(T_2-T_3)}{(T_0-T_2)(T_1-T_3)}
$$
in reduced form, of degree $m\le n/4-2$. Let $r$ count the points of $H$ with $R(x)\in\{0,1,\infty\}$. Then **$2r-3m\le9n/16=603,979,776$** for nonconstant $R$. Consequently these three fibers cannot give a first-prime quarter-rate three-head attack earlier than 480,946,859 errors. The three target values are the pair-collision values of this cross ratio and can be permuted. Arbitrary rational pencils remain open. [Exact three-head score](quarter-three-head-root-score.md) · [Cross-ratio pencil of four scalar functions](quarter-four-head-cross-ratio-barrier.md)

## Dividing the exponent differences

Subtracting the same exponent from all four preserves $R$. Divide all the resulting exponents by their positive gcd $g$, writing $R=R_0(X^g)$. The image of $H$ is $\mu_N$ with $N=n/k$, $k=\gcd(n,g)$. The degrees multiply, including any inseparable factor; each grid point downstairs has $k$ preimages. Thus an improved score upstairs would give $2r_0-3m_0>9N/16$ for the normalized map, with $m_0<N/4$. For $N\le32$ the known 32-site three-head bound excludes this: pulling back from $\mu_N$ to $\mu_{32}$ along $Y\mapsto Y^{32/N}$ retains the score density and gives degree below eight. The finite fiber bound is valid over the algebraic closure of the named field: in its only nontrivial septic test, two complete monic vanishers and a single grid equality determine the ratio scalar in the ground field. [Order-32 root count](quarter-three-heads-32-fibers.md#counting-incidences-across-the-32-quotient-fibers)

For $N\ge64$ write $m,r$ for the downstairs degree and count. Since $r\le3m$, an improvement implies $m>3N/16$ and $r>9N/16$. At each of these $r$ sites at least two of the four monomials agree. This also holds at a common zero of the unreduced products. Each unequal-exponent pair gives either zero or $\gcd(N,|a_i-a_j|)$ grid solutions. An equal-exponent pair gives none.

The primitive exponent set has both parities. If each parity occurs twice, at most four coincidences come from mixed parity pairs. If three exponents share a parity, the three mixed pairs give at most three. For the same-parity triple with distinct exponents, provided none of its grid gcds exceeds $N/4$, the two smaller gcds are equal and at most $N/8$ by the dyadic valuation. If two exponents there coincide, their pair has no solutions and the other two gcds are at most $N/4$ each. In all cases, if every nonzero gap had grid gcd at most $N/4$, the union would have size at most $N/2+4\le9N/16$. Thus **some nonzero exponent gap is a multiple of $N/2$**.

## The degree lost at triple coincidences

Order the exponents as $0=a_0\le a_1\le a_2\le a_3=L$, reordering the four monomials, which only permutes the three collision values. When the exponents are distinct, let $g_i$ be the gcd of the differences among the three exponents other than $a_i$. Then
$$
               m\ge L+(a_2-a_1)-\sum_{i=0}^3 g_i . \tag{1}
$$
Before dividing out common nonzero geometric roots, the degree is exactly $L+(a_2-a_1)$. Indeed two of the three pairing products have lowest exponent $a_0+a_1$ and highest $a_2+a_3$; they span the cross-ratio pencil by its difference identity.

At a nonzero root where just three monomials agree, the common order of the pairing products is the minimum vanishing order of the three differences in the coincident triple. For any triple this minimum, summed over all its common nonzero geometric roots, is either zero or its exponent gcd. Scaling by one common solution reduces the binomial gcd to $\gcd(X^u-1,X^v-1)=X^{\gcd(u,v)}-1$, including multiplicities. If all four values agree, the common order of the three pairing products is at most the sum of the four triple minima. To see this, let $w$ be the smallest pairwise difference order, and group the indices whose differences have order strictly greater than $w$. If every group has at most two elements, a perfect matching across groups costs $2w$. If one group has three elements, pair its closest-to-order-$w$ internal pair, of order $w'$, and use the remaining index to pair with the outside point. This costs $w'+w$ and the four triple minima sum to $w'+3w$. This proves (1) even when the starting exponents exceed the characteristic.

If just three exponents are distinct, any triple containing the two equal exponents has no common nonzero roots. For each of the other two triples the exponent gcd is one by primitivity. Hence $m\ge L-2\ge N/2-2$, impossible. If there are at most two distinct exponents, the primitive difference is at most one and the required large gap cannot occur.

## The only possible large-scale exponents

Now all four exponents are distinct. Every $g_i\le L/2$ since three points separated by multiples of $g_i$ lie in an interval of length $L$. The four gcds are pairwise coprime: the two corresponding triples share two indices and together their differences generate all exponent differences. Hence $g_i g_j$ divides the difference of the two shared exponents, and is at most $L$. Write $G=\max_i g_i$. If $G\le\sqrt L$ then their sum is at most $4\sqrt L$. Otherwise it is at most $G+3L/G$, which by convexity on $[\sqrt L,L/2]$ is at most $\max(4\sqrt L,L/2+6)$.

Put $M=N/4$ and first suppose $N\ge128$. Since $L\ge2M\ge64$, we have $L-4\sqrt L>M-1$. Equation (1) and $m\le M-1$ therefore force $L\le2M+10$. Also $G>L/3$. Otherwise the same convexity bound on $[\sqrt L,L/3]$ gives $\sum g_i\le\max(4\sqrt L,L/3+9)$, incompatible with (1) because $L/3+9<L/2$. Each other $g_i$ is now at most two, and at most one is two, so they sum to at most four. It follows from (1) that
$$
            G\ge M-3,\qquad a_2-a_1\le M+3-L/2\le3 .
$$
The three exponents corresponding to $G$ cannot include both internal exponents, whose gap is less than $G$. They therefore include both endpoints and form an arithmetic progression $0,G,2G=L$, since $3G>L$. The fourth exponent differs from $G$ by at most three. Every gap other than $L$ is then at most $G+3\le M+8<2M$. The required gap divisible by $N/2=2M$ must thus be $L=2M$, and $G=M$.

At $N=64$, an improved map has $13\le m\le15$ and $r\ge38$. The same maximum-gcd estimate gives $L\le42$, since for $L\ge43$ both $L-4\sqrt L$ and $L/2-6$ exceed 15. Exhausting the distinct primitive exponent triples $0<a_1<a_2<L\le42$ with $\sum_{i<j}\gcd(64,a_j-a_i)\ge38$ and right side of (1) at most 15 leaves just $(0,15,16,32)$ and $(0,16,17,32)$. Both have the same $0,M,2M$ triple. [Exact exponent census](../../../scripts/probes/probe_quarter_monomial_cross_ratio.py)

In the surviving shapes the $0,M,2M$ triple must have a nonzero geometric coincidence; otherwise its contribution to degree cancellation is zero, leaving degree at least $2M-4>M-1$. At one such coincidence the two short pair equations become the very same equation $X^M=\eta$. Its solutions are contained in the long pair equation $X^{2M}=\eta^2$. Thus on the grid the three pairs together cover at most $N/2$ sites. The remaining exponent is odd by primitivity, supplying at most three further sites against the even triple. This contradicts $r>9N/16$ and finishes the bound.
