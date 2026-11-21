# A polynomial certificate for the apolar predecessor argument

At length \(n=4h=2^{30}\), rate one half, and error allowance \(e=h-1\), the syndrome-pencil argument bounds the number of MCA-bad scalars by \(h+3\). The following gives a direct polynomial construction of the section used in that argument. It also gives a determinant proof of its first degree constraint. Both work in positive characteristic, including when some polynomial locators have repeated roots. [Threshold theorem and construction](rate-half-apolar-predecessor.md)

## A determinant on the parameter line

Use the parameter and coordinate projective lines in this order. Write \(S_j\) for the vector space of binary forms of coordinate degree \(j\), and \(d=2h-1\). Once at least \(e+2\) bad scalars have been selected, the maximal minors of the degree-\(e\) syndrome matrix vanish identically. Let \(f(t,y)\) be a primitive family of minimal apolar forms of bidegree \((l,r)\), \(r\le e\). Its coefficients in \(y\) have no common point on the parameter line, so every specialized \(f_t\) is a nonzero form of degree \(r\). The identity \(\lambda_t(f_t P)=0\) for every \(P\in S_{d-r}\) holds on the entire parameter line.

Set \(m=d-r+1\). Multiplication by \(f\) on the parameter line gives a quotient vector bundle
\[
 Q=(S_m\otimes\mathcal O)/(f\cdot S_{m-r}\otimes\mathcal O(-l)).
\]
The map is injective on every fiber, so \(Q\) has rank \(r\) and determinant degree \((d-2r+2)l\). Multiplication followed by the syndrome gives a map \(Q\to S_{r-1}^*\otimes\mathcal O(1)\). The transpose is injective at the generic parameter. A vector in its kernel would be an apolar form of degree \(r-1\). The nonzero determinant section therefore gives
\[
 (d-2r+2)l\le r.
\]
In particular \(3l\le e\). Injectivity at the generic parameter persists after extension to its algebraic closure, since a nonzero matrix minor stays nonzero.

The same degree bound follows directly from consecutive Hankel determinants. Choose two coordinate points away from the prescribed finite domain so that the two specializations of the locator have parameter degree $l$ and are coprime. Exclude the zeros of the leading parameter coefficient to select the first point. Its specialization has finitely many parameter roots. At each of those parameters the specialized coordinate form is nonzero by primitivity. To select the second point, also exclude the roots of these forms and the first point. A change of projective coordinate places the chosen points at zero and infinity. Write $c_0,\dots,c_r$ for the resulting locator coefficients and $a=d-2r+2$. Then $c_0,c_r$ have degree $l$ and are coprime.

Write $v_j=(\lambda_T(X^{j+i}))_{0\le i<r}$ and $D_j=\det(v_j,\ldots,v_{j+r-1})$, with these vectors as rows. For $0\le j<a$, apolarity gives $\sum_{i=0}^r c_i v_{j+i}=0$. In a determinant one can replace its first row by this linear combination with the last term moved to the other side. Rotating the replaced row to the end gives $c_0D_j=(-1)^r c_rD_{j+1}$. If $D_0=0$, there is a nonzero polynomial vector orthogonal to its first $r$ rows. The same recurrence and $c_r\ne0$ make that vector orthogonal to every row in the preceding-degree rectangular catalecticant, contrary to injectivity. Iterating the determinant identity and using coprimality gives $c_r^a\mid D_0$. Every entry of the initial block is affine in $T$, hence $al\le\deg D_0\le r$. The Lean code verifies the chart-point existence, recurrence, initial nonvanishing, divisibility and degree bound for the actual syndrome moment pencil. Its interface takes the rectangular kernel conditions and chart coefficients. [Hankel determinant proof](../../../ArkLib/Research/ProximityGap/Frontier/ApolarHankelMinors.lean)

## Division by a linear binary form

Let \(D\) be the divisor \(f(t,x)=0\). For homogeneous coordinate vectors \(x,y\), write \([x,y]=x_0y_1-x_1y_0\). On either standard coordinate chart of \(D\) form
\[
 q_x(y)=f(t,y)/[x,y].
\]
The numerator evaluates to zero at \(y=x\) in the coordinate ring of \(D\). After normalizing the nonzero coordinate of \(x\) to one, polynomial division is by a monic linear polynomial up to sign, hence is valid over this ring, including nilpotents. Uniqueness makes the quotients agree with their scaling on the overlap. Thus \(q_x\) has parameter degree \(l\), coordinate degree \(-1\) in \(x\) and degree \(r-1\) in \(y\).

For \(B\in S_m\), the quantity \(\lambda_t(q_x B)\) has bidegree \((l+1,-1)\) on \(D\). It is zero if \(B=[x,y]C\), because \(\lambda_t(f_t C)=0\). Evaluation of \(S_m\) at \(x\) is surjective onto \(\mathcal O_D(0,m)\) with precisely those multiples as kernel, as follows by the same monic division on either chart. Hence there is a section \(W\) of bidegree \((l+1,-m-1)=(l+1,r-2-d)\) with
\[
 \lambda_t(q_x B)=W(t,x) B(x).
\]
At every geometric point \(x\) of the generic fiber, \(q_x\ne0\). If \(W(t,x)=0\), then \(q_x\) is a degree-\((r-1)\) apolar form over the algebraic closure of the parameter function field, contradicting the generic matrix rank above. Thus \(W\) is a unit on the entire generic finite algebra after trivializing its line bundle. Because \(D\) is finite flat over the parameter line, passing to the generic fiber is injective on sections of any line bundle over every affine open of the base.

At a bad parameter let \(\lambda=\sum_j c_j\operatorname{ev}_{y_j}\), using just the distinct error sites with nonzero coefficients. They belong to the evaluation domain \(H\), and there are at most \(e\) of them. By apolarity,
\[
 0=\sum_j c_j f_t(y_j)P(y_j)\qquad(P\in S_{d-r}).
\]
Since \(d-r\ge e-1\), interpolation gives \(f_t(y_j)=0\) for every \(j\). The identity \([x,y_j]q_x(y_j)=0\) now holds in the full coordinate ring of the fiber. If \(K(x)\) is the domain vanisher then \([x,y_j]\) divides \(K(x)\), giving \(K(x)q_x(y_j)=0\). Consequently \(KW B(x)=0\) for every \(B\), and taking a locally nonvanishing monomial \(B(x)\) gives \(KW=0\) on the full fiber. The zero-syndrome case follows from the same formula with an empty sum. Lean verifies this identity in the quotient by the locator, after proving the reduction of the actual received-word syndrome to its error support under any coefficient extension. [Divided polynomial proof](../../../ArkLib/Research/ProximityGap/Frontier/ApolarDividedLocator.lean)

## The global degree obstruction

Let \(S\) be the product of the \(M\) distinct parameter factors from the bad fibers. Flatness over the parameter line makes each factor a nonzero-divisor. Thus \(U=W^4K/S\) is a section on \(D\) of bidegree
\[
 (a,b)=(4(l+1)-M,\ n+4(r-2-d)).
\]
If \(K|_D\ne0\), its restriction to the generic fiber is nonzero by flatness. Since \(W\) is a unit there, \(U\ne0\). Here \(b\le-8\). For a divisor of bidegree \((l,r)\) in the product of two projective lines, a section of coordinate degree \(b<0\) must have parameter degree \(a\ge l\). Indeed ambient \(H^0(\mathcal O(a,b))=0\), and for \(a<l\) the ideal term \(H^1(\mathcal O(a-l,b-r))\) vanishes because both twists are negative. Consequently \(M\le3l+4\le h+3\). This uses the elementary cohomology of line bundles on a projective line and the product formula over a field. [Cohomology of projective space](https://stacks.math.columbia.edu/tag/01XS) · [Künneth formula](https://stacks.math.columbia.edu/tag/0BEC)

If \(K|_D=0\), then \(K\) belongs to the principal divisor ideal, so \(l=0\) and \(f\) divides \(K\). This gives a fixed reduced support \(B\subset H\). The error coefficients of each original row descend to the original finite field because the evaluations at these distinct field points are linearly independent and their linear system has coefficients in the base field. On the complement of the active support, the two corrected rows give a joint explanation. A finite scalar can add agreement at an active support site only when its nonzero linear discrepancy vanishes. Unique decoding then bounds the bad scalars by \(|B|\le r\).

At the next radius, the two-head construction takes disjoint sets of \(h+1\) coordinates. Their complement vanisher has degree \(2h-2\), so both rows of the second head \((XD_0,-D_0)\) are allowed. For each coordinate \(x\) in either exceptional set, its own scalar \(\gamma=x\) adds the required agreement while the second row still disagrees there. Any joint explanation would be determined by the other \(3h-1\) core sites. This verifies the claimed \(2h+2\) distinct finite scalars. At the displayed Proth prime, modular exponentiation gives \(g^{2^{29}}=-1\), \(g^{2^{30}}=1\), and direct integer division gives budget \(h+3\). Together these facts give the written exact threshold \(1/4\) on this field. [Construction and prime](rate-half-apolar-predecessor.md)
