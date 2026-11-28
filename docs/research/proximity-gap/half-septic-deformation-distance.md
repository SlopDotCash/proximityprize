# Sharp distance from the first-prime half-rate septic construction

Let $n=2^{30}=16s$, with $s=67,108,864$, and let $H$ be the named first-prime subgroup. Take the four scalar polynomials from the half-rate witness at 313,174,699 errors. At each $x\in H$, prescribe every pair equality of their four septic values at $Y=x^s$, before introducing the common locator. A candidate quartet **breaks a site** when at least one prescribed equality there fails. Additional coincidences count as zero losses. [Septic polynomials, partitions and original witness](rate-half-seven-twenty-fourths.md)

For four arbitrary scalar polynomials of degree at most $8s-2=536,870,910$, the exact minimum positive number of broken sites is **134,217,730**. Any quartet breaking fewer has, after subtracting the first head, the form $A(X)F(X^s)$, where $F$ is the vector of the three original septic differences. The sixteen-fiber optimality theorem then excludes an earlier overrun explained by these four heads of nonconstant direction. In particular any four-head counterexample at the first unresolved error count must break at least 134,217,730 sites of every rotation and head relabelling of the displayed pattern. The unrestricted first-failure bracket is still 268,435,457 through 313,174,699. [Four-head necessity at the first unresolved count](four-head-partition-allocation.md) [Optimality within the sixteen-fiber class](rate-half-seven-twenty-fourths.md#the-same-optimum-when-a-label-can-use-several-fresh-agreements)

## The 28 quotient equations

Write $w$ for the named primitive sixteenth root. Subtract head zero and regard the remaining three polynomials as one vector. In the sixteenth-root quotient there are twelve sites carrying a triple, two sites with a single pair, and one with two pairs. A triple contributes two equality equations. Joining consecutive members of each equal block gives 28 equations on a three-vector $U(Y)$. Components of index zero in the formulas below mean the constant zero polynomial.

| Maximum degree of $U$ | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---:|---:|---:|---:|---:|---:|
| Kernel dimension | 0 | 1 | 2 | 3 | 5 | 8 |

For an equality $i=k$ at $y$, the entry in the column for $Y^a$ of head $v\in\{1,2,3\}$ is $(1_{i=v}-1_{k=v})y^a$. Row reduction over the actual named prime gives the table. Thus every solution through degree nine is a polynomial multiple of $F$. Choose a degree-ten solution $G$ independent of $F$ over the rational function field. The probe selects one by finding a quotient site where the two evaluated vectors are linearly independent. The degree-ten solution space consists of the four multiples $Y^aF$, $0\le a\le3$, and $G$. The same finite computation verifies that $F(w^j)\ne0$ for every $j$. [Exact kernel and derivative check](../../../scripts/probes/probe_half_septic_deformation_distance.py)

## The lower bound and its attainment

Let $U(X)$ be a normalized candidate vector of degree at most $8s-2$. Let $D$ be its set of broken sites, $b=|D|$ and $L_D=\prod_{x\in D}(X-x)$. The vector $L_DU$ satisfies every prescribed equality on every lifted fiber. Expand it uniquely as
$$
 L_D(X)U(X)=\sum_{a=0}^{s-1}X^a U_a(X^s).
$$
For each equation $i=k$ at $w^j$, the corresponding difference on the right becomes a polynomial of degree below $s$ after setting $X^s=w^j$. Its $s$ distinct roots in that fiber force every coefficient to vanish. Thus each $U_a$ satisfies the 28 quotient equations.

If $b\le2s+1$, then $\deg L_DU\le10s-1$, so every $U_a$ has degree at most nine. It follows that $L_DU=A(X)F(X^s)$. Since $F(x^s)\ne0$ at each point of $D$, the squarefree locator $L_D$ divides $A$. Cancelling it shows that $U$ satisfies every equality and $D$ is empty.

For attainment, choose any $2s+2$ sites from the thirteen quotient fibers where $G(w^j)=q_jF(w^j)$. These are all exponents except 3, 7 and 11. Choose a polynomial $A$ of degree at most $2s+1$ taking value $-q_j$ at each selected site in fiber $j$. Then
$$
 U(X)=\frac{A(X)F(X^s)+G(X^s)}{L_D(X)}
$$
is a polynomial vector of degree at most $8s-2$ satisfying all constraints outside $D$. Its numerator is independent of $F(X^s)$, so it must break at least one site. The lower bound now forces the broken set to be exactly $D$. If necessary, adding a constant multiple of $F(X^s)$ makes all four heads distinct, as each head pair excludes at most one constant. This addition preserves every broken-site decision. An explicit expansion on the actual prime field gives exactly ten broken sites at length 64 and thirty-four at length 256. [Small-length constructions and production arithmetic](../../../scripts/probes/probe_half_septic_deformation_distance.py)

## Every deformation through 201,326,593 broken sites

Suppose $2s+2\le b\le3s+1$. Now $\deg L_DU\le11s-1$, so the degree-ten kernel gives
$$
 L_D U=A(X)F(X^s)+B(X)G(X^s),\qquad \deg B\le b-2s-2 .
$$
The bound on $B$ follows because the residue coefficient $U_a$ can contain $G$ only if $10s+a\le 8s-2+b$. The polynomial $B$ is nonzero at every broken site $x$. Otherwise $A(x)=0$ since $F(x^s)\ne0$, and cancelling $X-x$ on both sides shows that $U$ satisfies the prescribed equalities at $x$.

Consequently all these deformations preserve the two single-pair fibers of exponents 3 and 11 everywhere. A broken site must have $G(x^s)=q_jF(x^s)$, and there are exactly the thirteen fibers listed above. At each such site differentiation shows that **every previously equal head pair becomes unequal**. Indeed for a prescribed pair $i,k$, put $f=F_i-F_k$ and $g=G_i-G_k$. Both vanish at $y=x^s$. Its new difference multiplied by $L_D'(x)$ is
$$
 s x^{s-1} B(x)\bigl(g'(y)-q_jf'(y)\bigr).
$$
The quotient computation verifies the last factor is nonzero for every prescribed pair at each of the thirteen eligible sites, including both pairs at exponent 15. This describes the possible losses even when the new polynomials have no symmetry. Whether their new pair coincidences ever improve the numerical MCA radius remains open.

## Four-head safety before 306,184,192 errors

A quartet breaking at most 201,326,593 of the prescribed sites cannot explain an overrun before **306,184,192 errors**. Here the heads may have arbitrary nonconstant polynomial direction, and a label may need several fresh agreements. At the first 17,895,697 open error counts every unrestricted overrun admits this four-head representation. Thus throughout that interval any overrun requires at least **201,326,594** changes against each rotation and head relabelling of the incumbent pattern. [Unrestricted four-head interval and repair of short cores](four-head-partition-allocation.md)

To prove this consider a positive distance $b$ in the stated range. Every broken site has maximum head multiplicity two. Indeed if three heads previously coincided then they become pairwise distinct, while at the double-pair site both previous pairs separate. On the exponent-seven fiber the four points $(F_i(w^7),G_i(w^7))$ have no three collinear, as verified by all four triangle determinants. Since this fiber contains no broken sites, the formula for $L_DU$ shows that whenever $B(x)$ is nonzero every equality block there has size at most two. Consequently the number $l$ of sites with maximum head multiplicity at most two satisfies
$$
 l\ge b+s-\deg B\ge3s+2.
$$

Suppose the four heads cover more than $n$ distinct bad labels. The short-core repair in the cited allocation proof gives a choice of ordinary blocks and holes of capacity at least $n+1$, with all four core sizes at least $n-e-1$. This uses the same scalar polynomials. Let $m_x$ be the matched block size, zero at a hole, let $E=\sum m_x$, and let $h,z$ be the numbers of holes and matches of size four. Each ordinary site with a foreign head supplies at most one label, a hole at most four, and a size-four match none. Hence $3h\ge z+1$. The six polynomial pair differences each have at most $8s-2$ roots. As $\binom m2-2m+3$ takes values $3,1,0,0,1$ for $m=0,1,2,3,4$, we have
$$
 z+3h\le 6(8s-2)-2E+3n.
$$
At each of the $l$ sites at most two heads can match. At any other site at most three match unless all four do. A hole lowers either bound by at least two. Therefore $E\le3n-l+z-2h$. Combining these inequalities gives
$$
 6l\le18n-6E+6z-12h
 \le18n-6E+z+3h-5
 \le21n+6(8s-2)-8E-5
 \le32e-8n+15.
$$
In the last step use $E\ge4(n-e-1)$. Substitution of $l\ge3s+2$ gives the claimed integer lower bound on $e$. The zero-distance case is already excluded through 313,174,698 errors by the sixteen-fiber theorem.
