# Rich witness lines at the rate-half predecessor

Let $H=\mu_n(\mathbb F_p)$, $n=2^{30}=4h$, $k=2h$, $e=h-1$, and suppose $p>48n^2$. Here and below the displayed hypotheses include $n\mid p-1$. Both production primes satisfy these conditions. Choose one degree-$<k$ decoding polynomial $q_\gamma$ for each of $e+2=268435457$ distinct MCA-bad scalars, with its non-jointly-explainable agreement witness. At least **44,739,243** of the points $(\gamma,q_\gamma)$ lie on no affine line containing eight selected points. Consequently every affine-line cover of the family needs at least **6,391,321** lines.

Thus the exact single-line maximum $e+1$ also applies to bad families covered by fewer than 6,391,321 affine witness lines. The unrestricted worst-case count at this predecessor remains open. This is a written theorem. The cited subgroup-curve bound is a published input.

## Overlaps of the exceptional coordinate sets

Put $t=n-e=3h+1$, $d=k-1=2h-1$. A line through two selected points has the form $q=A+\gamma B$, with $A,B$ polynomials of degree at most $d$. Let $C_i$ be the coordinates on which its pair $(A_i,B_i)$ equals the two received symbols. Write $E_i=H\setminus C_i$, $s_i=t-|C_i|$, and let $L_i$ count the selected points on the line. Each coordinate of $E_i$ can agree at most once as $\gamma$ ranges over this line. Each selected point needs at least one such agreement, since its witness has no joint explanation. If $|C_i|\ge t$, this gives $L_i\le n-|C_i|\le e$. Otherwise $L_i(t-|C_i|)\le n-|C_i|$. In particular every line holds at most $e+1$ selected points and has an outsider.

For any outsider, its polynomial minus $A_i+\gamma B_i$ is nonzero of degree at most $d$. It can agree at most $d$ times on $C_i$, hence must agree at least $t-d=h+2$ times in $E_i$. In particular
$$
b_i:=|E_i|-(h+2)=s_i-3\ge0,\qquad
L_i\le A(s_i):=1+\lfloor e/s_i\rfloor.
$$
Each outsider misses at most $b_i$ points of $E_i$.

Call a line rich if $L_i\ge8$. For distinct rich lines $i,j$, choose seven points on line $j$ outside line $i$. At each site of $E_i\cap E_j$ at most one of them agrees with the received fold, so at least six miss. Summing the seven miss budgets gives
$$
6|E_i\cap E_j|\le7\min(b_i,b_j).
\tag{1}
$$
The two orientations give the minimum. For $\min(b_i,b_j)\le5$, integrality sharpens (1) to $|E_i\cap E_j|\le\min(b_i,b_j)$.

There are at most four rich lines. Otherwise choose five. Each has $b_i\le\lfloor e/7\rfloor-3$. Bonferroni and (1), using $2\min(b_i,b_j)\le b_i+b_j$, give
$$
4h\ge\Big|\bigcup_{i=1}^5 E_i\Big|
\ge5(h+2)-\tfrac43\sum_i b_i>4h.
$$
The last inequality follows from $e=h-1$.

If there are four rich lines, order them by $s_1\le s_2\le s_3\le s_4$. Whenever $s_3\le8$, every pair has smaller $b\le5$. The sharp integer version of (1) and Bonferroni give
$$
4h\ge 4(h-1)+\sum_i s_i-
\big(3s_1+2s_2+s_3-18\big),
\quad\text{hence}\quad s_4+14\le 2s_1+s_2.
$$
It follows that either $s_1\ge7$ or $s_3\ge9$.

## Two lines of slack three

Suppose two distinct rich lines $i,j$ have $s_i=s_j=3$. Equation (1) makes $E_i,E_j$ disjoint, each of size $h+2$, and their common core has size $2h-4$. Divide $A_i-A_j$ and $B_i-B_j$ by the vanisher of this common core. The resulting polynomials $P,Q$ have degree at most three. At every point of $E_i$, line $j$'s polynomial pair equals the receiver while line $i$'s pair differs, so $P,Q$ cannot both vanish there. Each selected scalar on line $i$ needs three distinct fresh points of $E_i$, where $P+\gamma Q=0$. Since at least eight scalars have such a fiber, $Q\ne0$ and the reduced rational map $R=-P/Q$ is nonconstant of degree exactly three. The $L_i$ fibers give at least $6L_i$ ordered off-diagonal pairs $(x,y)\in H^2$ with $R(x)=R(y)$.

For any degree-three rational map in this characteristic, write $R=N/D$ in lowest terms. The off-diagonal collision polynomial
$$
\frac{N(X)D(Y)-N(Y)D(X)}{X-Y}
$$
has bidegree at most $(2,2)$. It has no vertical or horizontal components by coprimality and nonconstancy. It has no diagonal component because $R$ is separable. A translated-subtorus component has a parametrization $X=t^a, Y=c t^b$ over the algebraic closure, up to rescaling the parameter, with $a,b\ne0$ coprime. Comparing degrees in $R(t^a)=R(c t^b)$ yields $|a|=|b|=1$. The possibility $Y=c/X$ is an involution fixing $R$, which would force its degree to be even by the fixed-field degree formula. In the case $Y=cX$, the order of the deck rotation divides three by the same formula. It has order three since the diagonal was removed. Thus it contributes no points on the dyadic group $H^2$.

An absolutely irreducible remaining component of bidegree $(a,b)$ has geometric genus at most $(a-1)(b-1)$ on normalization in $\mathbb P^1\times\mathbb P^1$. Its coordinate functions have at most $2a+2b$ distinct zeros and poles, so its Euler characteristic in the sign convention of Corvaja–Zannier is $\chi\le 2ab$. Their Corollary 2 bounds the number of subgroup points by
$$
\max\{3(2n^2ab\chi)^{1/3},\;12n^2ab/p\}.
$$
The characteristic term is less than one. A single component of bidegree at most $(2,2)$ contributes at most $12n^{2/3}$. If there are two non-toric components, each has bidegree $(1,1)$, and together they contribute at most $6\sqrt[3]{4}\, n^{2/3}<12n^{2/3}$. All the off-diagonal pairs are therefore bounded by $12n^{2/3}$. Thus both lines of slack three have $L_i,L_j\le 2n^{2/3}=2097152$. [Corvaja–Zannier, JEMS, Corollary 2](https://doi.org/10.4171/JEMS/409)

## Production count

Write $U=2097152$. With at most three rich lines and at most one of slack three, their total size is at most $A(3)+2A(4)=223696214$. If at least two have slack three, the bound $2U+2A(3)=183151276$ suffices even with four rich lines. With four rich lines and at most one of slack three, the two possibilities from the four-set inequality give bounds $4A(7)=153391692$ and $A(3)+A(4)+2A(9)=216239674$. Thus all rich lines together cover at most 223696214 selected points. Every other line contains at most seven, yielding both bounds in the statement.

To attain the single-line maximum, put the received pair equal to $(0,0)$ on $t-1$ positions and to $(-x,1)$ on each remaining position $x$. These $e+1$ positions give distinct bad scalars $\gamma=x$ with witness the core plus their own position. Agreement on the core forces each explaining polynomial of degree less than $k$ to vanish identically.
