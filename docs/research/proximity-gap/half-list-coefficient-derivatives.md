# Half-rate list safety from derivatives of the differential equation's coefficient

On either named field, every closed ball through **314,991,700 errors** at rate $1/2$ contains at most **108,015 words**. This gives a first-failure floor of **314,991,701** for the two respective budgets $n$ and $2n$. The proof applies to every injective length-$n$ grid and every positive interleaving width. Its finite comparisons use exact arithmetic. [Executable certificate](../../../scripts/probes/probe_half_list_coefficient_derivatives.py)

Put $n=2^{30}$, $d=n/2-1$, $t=\lfloor\sqrt{nd}\rfloor-500000$, and $s=t/n$. Scalarize the interleaving over a finite extension and work over its algebraic closure. The primary hidden-derivative interpolation uses weights $1,d,d-1$ on $X,Y,V$, local order eleven, and derivative degree two. Its source surplus is **308,544,294**. Every word's jet lies on a primary factor of weight below $P=11t$. The total jet degree is at most $b_0=\lfloor(P-1)/(d-1)\rfloor=15$. [Interpolation and quotient proof](sixteenth-list-quotient-jets.md)

Assign words to factors containing their generic jets. Factors independent of $V$ contain at most $b_0$ words in total. There are at most two other factors. Call a group large at size $L=54000$. For a large group on an irreducible equation of positive derivative degree $v$ and weight $w$, choose $t$ agreements of each word after deleting the exceptions specified below. Write $p_x$ for the proportion of retained words selecting site $x$, and $\mathbb E$ for averaging over the sites. Pairwise agreement is at most $d$, so
$$
 \mathbb E p=s,\qquad
 \mathbb E(p-s)^2\le \sigma^2,\qquad
 \sigma^2=d/n-s^2+(s-d/n)/(L-b_0^2).
$$
Write $o_x$ for the order of the equation under $X=x+u$, $Y=y_x+uz$, $V=z+uz_1$ with $z,z_1$ independent. The local quotient proof gives $o_x\le w/d+v$. Its ordinary $V$-derivative bound, after removing at most $b_0^2$ singular generic jets, gives
$$
 \mathbb E o_x\le 1+(w-d+1)/t+(w/d+v)\sigma/(2s).
$$

## Vertical derivatives and the common factor of the coefficients in $X$

For $v=1$ write $g=A(X,Y)+B(X,Y)V$ with $B\ne0$. Put $a=\deg_Y B$, $b=\lfloor w/d\rfloor$, $K=b+1$, and $E=w-d+1$, the weight bound for $B$. For $0\le j\le a$ define
$$
 \phi_j(o)=\max\{o-1-j,\ {\bf1}_{o\ge j+1}\}.
$$
At every hit of any polynomial word, $\partial_Y^j B(X,f)$ vanishes to order at least $\phi_j(o_x)$. For $o=o_x\ge1$, the coefficient of $z_1$ gives ordinary plane multiplicity at least $o-1$ for $B$, and the constant term gives the same for $A$. With $U=X-x$, $Z=Y-y_x$, and $m=o-1$, their homogeneous terms of degree $m$ satisfy
$$
                  U A_m+Z B_m=0 .
$$
In particular $U\mid B_m$, including the case $m=0$ where $B_m=0$. Hence all powers of $Z$ below $o$ vanish in $B(x,y_x+Z)$. This proves the indicator in $\phi_j$. Ordinary plane multiplicity after $j$ derivatives gives the other term.

Each $\partial_Y^jB$ is nonzero, as $a$ is smaller than the characteristic. Delete all group words on which one of them vanishes identically. There are at most $\sum_{j=0}^a(a-j)\le b_0^2$ by the root count over $k(X)$. Evaluation and root counting give $\mathbb E[p\phi_j(o)]\le(E-jd)/n$. For $j=a$ the derivative is a fixed univariate polynomial, so one can count across all sites.

Factor $B=C(X)B_0(X,Y)$ with $B_0$ primitive as a polynomial in $Y$, and write $c=\deg C$, $h_x=\operatorname{ord}_x C$. If $h_x=0$, the nonzero specialization $B(x,Y)$ of degree at most $a$ gives $o_x\le a$. If $h_x>0$, the ordinary multiplicity of $B_0$ is at most $a$ because $B_0(x,Y)\ne0$. Hence $o_x\le h_x+a+1\le a+2h_x$. It follows that $2c/n\ge\mathbb E o-a$.

On any retained word the evaluation of $B_0$ is nonzero and of degree at most $E-c$. At a hit it has order at least $(o-1-h_x)_+$. Therefore
$$
 \mathbb E[p o]\le s+(E-c)/n+
     \mathbb E[p\min(h_x,(o-1)_+)]
 \le s+E/n-(1-s)c/n+\sigma K/2 .
$$
The covariance bound here uses the standard deviation of $p$ and half the range of the bounded function. Combining this with $\mathbb E[p o]\ge s\mathbb E o-\sigma K/2$ yields
$$
 \left(s+\frac{1-s}{2}\right)\mathbb E o
 \le s+E/n+(1-s)a/2+\sigma K .                                  \tag{1}
$$

Use the content in each derivative bound as well. For a site of order $o$ put
$$
 H(o)=\begin{cases}0 &o\le a,\\ \max(1,o-a-1)&o>a,\end{cases}
 \qquad
 Q_j(o)=
 \begin{cases}\phi_j(o)&o\le a,\\(o-j-1-H(o))_+&o>a.\end{cases}
$$
The preceding multiplicity bounds give $h_x\ge H(o_x)$. Each nonzero $\partial_Y^j B_0$ evaluates to a polynomial of degree at most $E-c-jd$. It has multiplicity at least $(o-j-1-h_x)_+$ at a hit, and at least $\phi_j(o)$ if $h_x=0$. If $h_x>0$, the site cost $h_x+p_x(o-j-1-h_x)_+$ is nondecreasing in $h_x$, since $p_x\le1$. For $o\le a$ it is at least $p_x\phi_j(o)$, since $h_x\ge1$ also pays for the indicator. Adding the content degree over the sites and the evaluated degree on the words therefore gives
$$
 \mathbb E[H(o)+p Q_j(o)]\le (E-jd)/n .
$$
For $j=a$ this inequality holds with $p=1$, since the derivative is univariate. For $j<a$ the certificate uses
$$
 \mathbb E[H(o)+sQ_j(o)]\le(E-jd)/n+
           (\sigma/2)\max_{0\le u\le K}Q_j(u).                   \tag{2}
$$
The deleted words for $B$ and its $Y$-derivatives include all exceptions for $B_0$, since the content $C$ is independent of $Y$.

The two further inputs are $0\le o\le K$ and the plane coefficient intersection estimate
$$
 \mathbb E\max(0,o^2-o-1)\le [aw+bE-dab]/n.                    \tag{3}
$$
This uses the actual degree $a$ of $B$ and the upper bound $b$ for $\deg_Y A$. When $A=0$, irreducibility gives $g$ proportional to $V$. Its constant polynomial solutions have pairwise disjoint agreement sets and hence number at most $n/t<L$. [Plane intersection proof](linear-contact-quotient.md)

## Covering the integer weights

Write $N(w,h)$ for the source dimension at strict weight $w$ and derivative cap $h$, and $C(r,h)$ for the local jet rank. A large group on a factor is impossible whenever
$$
 N(rt,h)-N(rt-w,h-v)>
 n\,[C(r,h)-C(r,h-v)+(C(r,h-v)-C(r-1,h-v))\mathbb E o].        \tag{4}
$$
The quotient then provides a coprime secondary equation on the entire group. Its Bézout bound $b_0\lfloor(rt-1)/(d-1)\rfloor$ is smaller than $L$. Deletions used to bound the mean affect only the estimate for the common orders in (4).

Set $r=2500$. For $v=2$ on $2(d-1)\le w<P$, and for $v=1$ on $10d\le w<P$, the ordinary derivative estimate proves (4). The endpoint surplus lower bounds on those two intervals are **7,852,932,683,832** and **234,096,276,984,945**, respectively.

For $v=1$ on $d-1\le w<10d$, break at the changes in the two integer degree caps. For every possible $a$ the verifier takes nonnegative rational combinations of (1), (2), its univariate version, and (3). If the respective bounded functions are $H_i(o)$ and the chosen multipliers are $\lambda_i$, it adds the exact constant
$$
   \max_{u\in\{0,\ldots,K\}}
           \left(u-\sum_i\lambda_i H_i(u)\right).
$$
This gives a certified affine upper bound for $\mathbb E o$ on each interval. A floating-point optimizer proposes the multipliers. Their signs, the pointwise upper bound, and both final comparisons use rational arithmetic, so correctness does not depend on optimizer accuracy. One secondary cap and one affine mean bound pass at both ends. The source difference in (4) is concave in $w$, since its subtracted term is a sum of positive parts of affine functions. Thus (4) holds everywhere between them. Across all **104** checked linear intervals, the minimum endpoint surplus is **1,401,778,535,930**.

Every group has fewer than $L$ assigned words. The list size is consequently at most $2L+b_0=108015$.
