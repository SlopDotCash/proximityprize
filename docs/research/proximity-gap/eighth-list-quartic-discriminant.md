# Eighth-rate list safety from the quartic discriminant

On the first named prime at rate $1/8$, every closed ball through **704,116,763 errors** contains at most $n$ words. Thus the first failing error count is at least **704,116,764**. The proof covers every injective length-$n$ grid and every positive interleaving width. [Exact verifier](../../../scripts/probes/probe_eighth_list_quartic_discriminant.py)

Put $n=2^{30}$, $d=n/8-1$, $t=\lfloor\sqrt{nd}\rfloor-10000000$, and $L=\lfloor n/40\rfloor$. Use the cubic primary interpolant at order eight. Its surplus is **898,972,636** and its total jet degree is at most $b_0=\lfloor(8t-1)/(d-1)\rfloor$. Assign each word to a factor. At each group of at least $L$ words take its irreducible factor; let $g$ be the squarefree product of these factors of positive derivative degree. The small and derivative-independent groups together cost at most $3L+b_0$. [Cubic primary and joint interpolation](joint-list-contact-boards.md)

With the same adaptive parameters as the preceding first-prime eighth-rate board, the joint comparison excludes weight at least $3(d-1)$ for products of derivative degree two or three. Their respective minimum surpluses are **79,653,673,957,831** and **426,370,210,882,098** on the new input. Derivative degree three is impossible. A surviving degree-two product has total jet degree at most two and its normalized curve bound, including the small groups, fits $n$. The uniform linear coefficient intersection, applied without any exterior word, excludes weight $w\ge6d-1$ for a single large linear factor with minimum surplus **13,455,791,780,455**. [Normalized curve count](first-order-normalized-curve.md) · [Linear coefficient estimate](linear-contact-quotient.md)

Write such a linear factor as $g=A(X,Y)+B(X,Y)V$. Its weight is below $6d-1$, its total jet degree is at most five, and $a=\deg_Y B\le4$. First suppose $a=4$ and $B$ is squarefree over $k(X)$, where $k$ is the algebraic closure of the scalarized alphabet. Its weight satisfies $5d-1\le w\le6d-2$. At a physical point $(x,y)$ write $o$ for the radial contact order of $g$. The vertical derivative bound gives
$$
 \operatorname{ord}_x\big([Z^j]B(X,y+Z)\big)\ge
 \phi_j(o)=\max\{o-j-1,{\bf1}_{o\ge j+1}\}.
$$
This follows by evaluating the $j$th vertical derivative on the constant word $y$ and dividing by $j!$. The degree cap gives $0\le o\le w/d+1<7$. [Vertical derivative proof](half-list-coefficient-derivatives.md)

Write $E=w-d+1$. The $j$th coefficient of the unshifted quartic has $X$-degree at most $E-jd$. The quartic discriminant has degree six in the coefficients, and the coefficient indices of each monomial sum with multiplicity to twelve. Therefore its $X$-degree is at most $6E-12d$. It is nonzero by squarefreeness, and translation by the constant $y$ preserves it. If its coefficient-exponent vector is $\alpha$ for a monomial, the latter has $x$-order at least $\sum_{j=0}^4\alpha_j\phi_j(o)$. The minimum over the sixteen monomials, for $o=0,1,\ldots,6$, is respectively
$$
                        0,\ 0,\ 1,\ 3,\ 7,\ 12,\ 18 .
$$
The verifier obtains the monomials from the Sylvester determinant of $B,\partial_YB$ divided by the leading coefficient. Thus the discriminant order is at least $2o-3$ at each site, including specializations where the quartic loses degree. Summing gives
$$
 \mathbb E o \le \frac32+\frac{6(w-d+1)-12d}{2n}.
$$
This affine upper bound in the uniform quotient test, with local order $3000$ and derivative cap $1500$, gives an endpoint surplus of at least **55,779,081,227,643** across $[5d-1,6d-2]$. The quotient surplus is concave in $w$ and the Bézout bound is smaller than $L$. A large group with a squarefree quartic denominator is therefore impossible.

For the remaining linear equations write $b=\deg_Y A\le5$ and let $i$ be the number of distinct finite poles of $V=-A/B$ on the projective $Y$-line over an algebraic closure of $k(X)$. The two polynomials are coprime. The poles at finite $Y$ have total order $a$ and their number is $i$. At infinity the pole order of $V$ is $\max(0,b-a)$. In the local derivative calculation the pole increase at a finite pole of order $h$ is at most $h+1$, and at infinity is at most $(b-a-1)_+$. Thus the total increase per derivative is at most
$$
                      a+i+(b-a-1)_+ .
$$
For $a\le3$ this is at most seven. For a nonsquarefree quartic, $a=4$ and $i\le3$, again giving at most seven. The initial pole degree of $V$ is at most five. The normalized linear equation has at most $5+7d$ isolated polynomial solutions, or at most $(n-d)/(t-d)$ solutions in an integral family. When $A=0$ the constant solutions instead number at most $n/t$. There are no singular solution jets for a primitive linear equation over $k(X)$. [Derivative and integral-family proofs](first-order-normalized-curve.md)

Both population bounds fit the budget after adding $3L+b_0$. This completes the all-center estimate.
