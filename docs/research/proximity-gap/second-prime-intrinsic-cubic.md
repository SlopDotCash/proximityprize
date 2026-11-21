# A cubic incidence bound at 396013787 agreements

For the second named rate-sixteenth instance, the operational real supremum is at least $677728038/1073741824$. We prove goodness at $e=677728037$ errors. This is a written deduction; the integer comparisons are executable. Use $n=2^{30}$, $d=2^{26}-1$, $t=396013787$, and $k$ the algebraic closure of the prime field. Suppose there were $2n+1$ distinct MCA-bad labels, each with a polynomial witness $q_z$ of degree at most $d$ and at least $t$ agreements with the received affine rows.

## A cubic factor carries almost every label

The monomials $X^aZ^iY^j$ with $j\le3$, $i+j\le13$, and $a+jd<t$ outnumber the $14n$ site-line constraints by $70683404$. A nonzero such interpolant vanishes on all selected $(z,q_z)$. If every irreducible factor has $Y$-degree at most two, the linear and quadratic factor counts in the [second-prime low-degree argument](PROGRESS.md#low-degree-factors-of-the-quartic-cannot-carry-a-second-prime-violation) apply here. For clarity, the linear nonhead proof uses only $m\le34$ and the lower bound $t\ge357913943$. The quadratic proof discards at most $t-1-2d$ sites where the leading $Y$ coefficient is identically zero, so its bound $2d+1-\lceil70n/2048\rceil$ for the number of identity sites holds at the present $t$ as well. The squarefree discriminant step uses $2t<p$. The two conclusions are at most 184 points for a nonhead linear factor, and 4128 for an irreducible quadratic. Each actual affine head carries at most $e+1$ MCA-bad labels at the present radius by fresh-site counting. Since $e+1>4128$, all the factors together yield at most $3(e+1)+13<2n$ labels. Hence there is an irreducible cubic factor $F$, primitive over $k[X]$, of total $(Z,Y)$-degree $m\le13$. Its remaining factors have degree zero in $Y$, so at least $M=2n+1-13=2147483636$ selected points lie on $F$.

## Bounding the total multiplicity

Use the section-space dimension $D(h,v)$ and weight $W$ defined in the [quartic elimination](second-prime-quartic-intrinsic.md). Put $h=2^{27}$. Every interpolant of total $(Z,Y)$-degree at most $h$ and weight below $t$ is divisible by $F$ if it vanishes on each received site-line, since $M>13h$. The dimension lower bound and the two consecutive quotient capacities are
\[
\begin{split}
D(h,t)-(h+1)n&=39689247649679397,\\
D(h-3,t-230335609)&=39689247776542851,\\
D(h-3,t-230335610)&=39689247373889676.
\end{split}
\]
Thus $3d\le W\le230335609$.

The second scalar derivative numerator $N$ in the quartic proof has $Y$-degree at most seven here and weight at most $3W-2d$. If $F\mid N$, the inverse-derivative argument splits $F$ into three affine lines over $\overline{k(X)}$, each accommodating at most one selected point. Otherwise its resultant with $F$ has $X$-degree bounded by
\[
 H=7W+3(3W-2d)-21d=16W-27d\le1873430443.
\]
Define $r_x\in\{0,1,2,3\}$ as the order of $F(x+T,Z,L_x(Z)+V)$ in $(T,V)$ over $k(Z)$. At every site of positive order the local intersection with $N$ is at least $r_x(3r_x-2)\ge7r_x-6$, by the argument in the quartic proof. With $R=\sum r_x$ this gives $R\le\lfloor(H+6n)/7\rfloor=1187983055$.

## Imposing polynomial jet membership

Set $\mu=3000$, $s=715000000$, and $A=\binom{\mu+1}{2}=4501500$. For the unknown $P$, take $j\le2$, $i+j\le s$, and $a+jd<\mu t$ in the monomial parametrization above. There are
\[
 C=\sum_{j=0}^2(s-j+1)(\mu t-jd)=2548204770833999217726
\]
coefficients. At each of all $n$ sites choose independent monomial translates of the jet of $F$ spanning the image of multiplication by it in $k(Z)[T,V]/(T,V)^\mu$. Their number is $A-w_x$, where $w_x=\mu r_x-\binom{r_x}{2}$. All their coefficient entries are polynomials of $Z$-degree at most 13. Give each basis column an independent unknown scalar polynomial of $Z$-degree at most $s-13$. Require the sum of the resulting columns to equal the translated jet of $P$ as polynomial vectors in $Z$. Both sides have degree at most $s$. These $A(s+1)$ scalar linear equations add $(A-w_x)(s-13+1)$ auxiliary unknowns, for a net cost of at most $(s+1-13)w_x+13A$ equations. If the jet of $P$ is zero the multipliers at that site are all zero by independence over $k(Z)$. Thus a nonzero solution of the simultaneous system necessarily gives $P\ne0$.

Since $\binom{r_x}{2}\ge r_x-1$ even for $r_x=0$, one has $\sum w_x\le(\mu-1)R+n\le3563834923769$. The total net cost is at most
\[
 (s+1-13)\,3563834923769+13nA=2548204762563485482772.
\]
The surplus $8270513734954$ is positive. Choose a nonzero solution $P$. Polynomial jet membership specializes at every scalar without any excluded pivot. For each selected point on $F$, substitute $Y=q_z(X)$; at every agreement $P(X,z,q_z)$ acquires a root of multiplicity $\mu$. Its degree below $\mu t$ forces it to vanish identically. But the nonzero scalar resultant $\operatorname{Res}_Y(F,P)$ has degree at most $3s+2(13-3)=2145000020<M$. This contradiction proves the claimed Hamming-step lower endpoint. [Integer certificate](../../../scripts/probes/probe_second_prime_intrinsic_cubic.py)
