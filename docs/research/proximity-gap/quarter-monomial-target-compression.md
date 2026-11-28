# Arbitrary target triples on large primitive monomial quotients

Let $R$ be a nonconstant cross ratio of four different scaled Laurent monomials over the algebraic closure of the first named field. Normalize their exponent differences to have gcd one, and write $N$ for the resulting dyadic grid size as in the fixed-target proof. If $2^{18}\le N\le2^{30}$ and $\deg R<N/4$, then for **any three different projective targets**, the number $r$ of their sites in $\mu_N$ satisfies
$$
                     r<9N/16 .
$$
Since $r\le3\deg R$, this implies $2r-3\deg R\le9N/16$ and excludes every target projectivity at these scales. On the original first-prime subgroup it excludes all such pencils whose normalized quotient has at least 262,144 sites. The cited fixed-target result separately covers the three pair-collision targets at every scale. [Quartic exponent span and gcd bounds](quarter-monomial-cross-ratio.md) · [Named three-head score](quarter-three-head-root-score.md)

Write the four exponents as $a_i$. Two facts from the exponent proof are used here; their proofs concern the monomials, independent of targets. First, **at most $N/2+4$ sites have any pair of monomial values equal**. If all nonzero exponent gaps have grid gcd at most $N/4$, this follows by splitting the primitive tuple into its two parities. If a larger gcd occurs, the degree bound forces, up to translation, the shape $0,N/4,N/2,N/4+b$ with $b$ odd and $|b|\le3$. The three even monomials have a geometric coincidence. Their two short pair equations coincide and are contained in the long pair equation, so their union and the three mixed pairs have at most $N/2+3$ grid points. The second fact is that if exactly three original exponents are distinct, their span is at most $\deg R+2$. [Exponent degree proof](quarter-monomial-cross-ratio.md#the-degree-lost-at-triple-coincidences)

## Compressing three frequencies at once

Take $K=49$. The three signed differences of opposite exponent sums are
$$
        l_1=a_0+a_1-a_2-a_3,\quad
        l_2=a_0-a_1+a_2-a_3,\quad
        l_3=a_0-a_1-a_2+a_3.
$$
Partition $[0,N)^3$ into $K^3$ boxes with side $N/K$. Two of the $K^3+1$ triples $(j l_i\bmod N)_{i=1}^3$, $0\le j\le K^3$, fall into the same box. Subtract to obtain $1\le h\le K^3$ and integers $L_i\equiv h l_i\bmod N$ of absolute value strictly below $N/K$. The $L_i$ have the same parity $\epsilon\in\{0,1\}$. Define four integer exponents $b_i$ by subtracting $\epsilon$ from each of
$$
 L_1+L_2+L_3,\quad L_1-L_2-L_3,\quad -L_1+L_2-L_3,\quad -L_1-L_2+L_3
$$
and dividing by two. Then $b_i-b_j\equiv2h(a_i-a_j)\pmod N$. The six pair sums $b_i+b_j$ are exactly the values $\pm L_k-\epsilon$ with multiplicity. Their span is less than $2N/K$. Also $2h<N$ and primitivity implies that the $b_i$ cannot all coincide.

Write $v=\gcd(2h,N)$ and consider each coset $tH^{2h}$ of $H=\mu_N$. For $x=tu^{2h}$ with $u\in H$, the monomial values differ from $c_it^{a_i}u^{b_i}$ by the same common nonzero factor. Call these the compressed monomials. On a coset where they have nonconstant cross ratio, each target has a nonzero unreduced pairing equation with exponents in the above interval of width below $2N/K$. Every original match solves this equation, including original common zeros of the pairing products. Dividing the $u$ count by $v$ therefore gives at most the proportion $6/K$ of the coset for all three targets combined.

## Counting the remaining cosets

A coset is exceptional if two compressed monomials are identical or if four different compressed monomials have constant cross ratio. In the first case **every physical site** of that coset has an equal pair of original monomial values.

For four different compressed monomials with nonconstant exponent tuple, constant cross ratio requires exactly one pair of equal exponents. The two coefficients in this pair are opposite. The other exponents lie symmetrically about that exponent, and the product of their coefficients is the square of either paired coefficient. To check this, if all four exponents are different, two of the three pairing products have different orders at zero after sorting. If three exponents coincide, applying a projectivity through three distinct constants to the remaining nonconstant monomial is nonconstant. In the other cases with a repeated exponent divide all four monomials by its monomial power. Two are nonzero distinct constants $A,B$, and the other two are varying monomials $C u^j,D u^k$. A constant cross ratio gives a projectivity fixing both $A,B$ and carrying the first varying monomial to the second; this follows by using $(z-A)/(z-B)$ as target coordinate. Equality of rational degrees gives $|j|=|k|$. For $j=k$ the projectivity would be a scaling fixing $A,B$, which would make the two monomials identical. For $j=-k$ it must be $z\mapsto CD/z$, giving exactly $B=-A$ and $CD=A^2$.

If there is no such harmonic coset, every exceptional site belongs to the first case and the bound $N/2+4$ above applies. Otherwise exactly one pair $i,j$ of compressed exponents is equal, independent of the coset. Every exceptional coset has $T_i=T_j$ or $T_i=-T_j$ at all its sites. When the actual exponents $a_i,a_j$ differ and their grid gcd is at most $N/4$, these two equations cover at most $N/2$ sites. If their grid gcd were larger, the original tuple would have the three-even, one-odd shape above. Since $N/v$ is even, $b_i=b_j$ forces $a_i,a_j$ to have the same parity, hence both even in that shape. The other two original exponents $a_k,a_l$ then have opposite parity. Compressed symmetry would force $N/v\mid a_k+a_l-2a_i$, an impossibility.

Finally consider $a_i=a_j$. Their original coefficients are distinct, so an exceptional coset must be harmonic. If the other two original exponents were equal, their compressed exponents would also agree, already excluded. The necessary product identity on the coset gives
$$
                    x^{a_k+a_l-2a_i}=c_i^2/(c_kc_l).
$$
The absolute exponent is at most twice the original span, hence at most $2(\deg R+2)<N$. If the exponent is nonzero, the equation has at most $N/2$ grid roots. If it is zero, an exceptional coset would impose $c_kc_l=c_i^2$ and $c_j=-c_i$ already on the original coefficients. The original rational cross ratio would be constant by the same reciprocal identity. Thus in every case the exceptional cosets contain at most $N/2+4$ physical sites.

With $C=N/2+4$ the resulting bound is $r\le C+(N-C)6/49<9N/16$ at every claimed dyadic size. The proof is written. The verifier checks the exact compression on the actual grid sizes, all numerical cutoff inequalities, and the classification of 10,400 different compressed four-monomial tuples in the small field of order 257, including 32 harmonic cases. [Finite verifier](../../../scripts/probes/probe_quarter_monomial_target_compression.py)
