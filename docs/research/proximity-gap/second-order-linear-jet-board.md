# A second-derivative interpolation board linear in the highest derivative

For a received word on an injective grid, take a polynomial of the form
$$
 F(X,Y,V,W)=A(X,Y,V)+B(X,Y,V)W
$$
with separate derivative-degree caps $\deg_V A\le h_A$ and $\deg_V B\le h_B$. A word $f$ is evaluated at $(X,f,f',f'')$. The exact local constraint count below applies without prescribed derivative values at the received points. First- and higher-derivative decoding on arbitrary domains is established by [Dao, Kominers and Thaler](https://eprint.iacr.org/2026/2056).

## Local rank and the boundary layer

Translate the received point to $(X,Y)=(0,0)$ and write $u=X$. For any graph through it put $z=f/u$, $w=z'$, $e=z''$. Then
$$
          Y=uz,\qquad V=z+uw,\qquad W=2w+ue.
$$
For universal contact of order $r$ take the polynomial image of this substitution modulo $u^r$, regarding $z,w,e$ as independent. Its vanishing suffices for every actual graph through the point. Assume the characteristic is zero or larger than the caps and contact orders, and greater than two.

Let $C(r,h)$ be the first-derivative [local rank](sixteenth-list-quotient-jets.md#the-local-quotient). At exact grade $q$ its space of leading terms is the span of the monomials $z^i w^j$ indexed by
$$
  E(q,h)=\{(i,j):0\le j\le\min(h,\lfloor q/2\rfloor),\quad
                         0\le i\le q+h-3j\}.
$$
Indeed first-order source monomials $u^aY^bV^k$ group by $b_0=a+b$ and $m=b+k$. In one block the consecutive derivative exponents run from $\max(0,m-b_0)$ to $\min(h,m)$. Its independent leading rows are indexed by $j$ starting at zero up to one less than the number of exponents, by binomial Vandermonde elimination. The resulting term has grade $q=b_0+j$ and ordinate exponent $i=m-j$. Substitution of these two equalities gives precisely $E(q,h)$. Distinct triples $(q,i,j)$ belong to distinct row positions, so cancellations across blocks impose no further conditions.

For the second-order board, the coefficient of $e$ is $u$ times the local first-order image of $B$. It accounts for $C(r-1,h_B)$ conditions. In its kernel $B$ vanishes to order at least $r-1$. The remaining component of the map is the first-order image of $A$ together with $2w$ times the grade-$(r-1)$ image of $B$. The latter contributes exactly the leading monomials outside the grade-$(r-1)$ space of $A$. Thus the exact image dimension is
$$
 C_2(r,h_A,h_B)=C(r,h_A)+C(r-1,h_B)
   +\big|\{(i,j+1):(i,j)\in E(r-1,h_B)\}\setminus E(r-1,h_A)\big|.
$$
In particular the boundary correction for $h_A=h_B=h$ is exactly $r+h$, one new monomial for each $i=0,\dots,r-1+h$. The finite verifier separately expands all the monomials in four variables and reduces 336 matrices over two prime fields. [Independent rank checks](../../../scripts/probes/probe_second_order_linear_jet_board.py)

Give $X,Y,V,W$ weights $1,d,d-1,d-2$. The number of monomials with weight strictly below $rt$ is $N(rt,h_A)+N(rt-d+2,h_B)$ with the first-order source count $N$ defined in the local quotient proof. If this exceeds $nC_2$, there is a nonzero $F$ satisfying all the local constraints. A degree-at-most-$d$ word with $t$ agreements gives at least $rt$ zeros in a polynomial of degree less than $rt$, hence $F(X,f,f',f'')=0$ identically.

## A finite candidate bound from two Taylor initial parameters

Take $d\ge2$, $n\ge t>d$, and work over an algebraically closed field of the indicated large characteristic. Let $b$ bound the total degree of $F$ in $Y,V,W$. The factors not involving $W$ together have first-order candidate bound
$$
  2bh_A-h_A^2+b+d(4bh_A-2b-2h_A^2)+h_A(n-d)/(t-d)
$$
by the [normalized-curve count](first-order-normalized-curve.md), for $h_A\ge h_B$ and $h_A\le b$. In these applications the characteristic exceeds $\max(rt+1,2b^3+2,d+1)$.

There is at most one irreducible factor involving $W$; write it as $A_1+B_1W$ with coprime coefficients in $K[Y,V]$, $K=k(X)$. At most $b^2$ polynomial words on this factor satisfy both $A_1(X,f,f')=0$ and $B_1(X,f,f')=0$ by plane Bézout applied to their distinct generic jets. For every other word on the factor, $B_1(X,f,f')$ is nonzero. Use the derivation $\delta$ on $K(Y,V)$ with $\delta X=1$, $\delta Y=V$, $\delta V=-A_1/B_1$. For $j\ge2$ we have $\delta^jY=P_j/B_1^{2j-3}$. With $D_0=B_1\partial_X+B_1V\partial_Y-A_1\partial_V$, the recursion is
$$
 P_2=-A_1,\qquad P_{j+1}=B_1D_0(P_j)-(2j-3)P_jD_0(B_1).
$$
In the two variables $Y,V$, $\deg B_1\le b-1$, $\deg A_1\le b$. Thus $\deg P_j\le b+(j-2)(2b-2)$.

Choose a transcendental initial coordinate $\xi$ over the coefficient field of the finite list, its received word and the interpolation data, and work over an algebraic closure containing $\xi$. The generic degree-$d$ Taylor polynomial with initial value and derivative $(u,v)$ is
$$
 P(X,u,v)=\sum_{j=0}^d \frac{(X-\xi)^j}{j!}
                         (\delta^jY)(\xi,u,v).
$$
This is used only for *recovering actual solutions*. Each regular polynomial word on the factor occurs on substituting $(u,v)=(f(\xi),f'(\xi))$, since its derivatives satisfy the stated recursion and Taylor expansion is exact. These initial pairs are distinct. The common denominator $Z=B_1(\xi,u,v)^{2d-3}$ is nonzero at them. The degree in $(u,v)$ of $Z$ and of each coefficient of $ZP$ is at most $L=1+(2d-3)(b-1)$ by the numerator bound. In particular $P(\xi,u,v)=u$ and $\partial_X P(\xi,u,v)=v$.

At each site put $T_x(u,v)=Z(P(x,u,v)-y(x))$, a polynomial of degree at most $L$. At most $d$ sites have $T_x$ identically zero: otherwise the $d+1$ prescribed values would determine $P$ independently of $u,v$. Fix a site with $T_x\ne0$ and an irreducible factor $G$ of $T_x$ not dividing $Z$. On the curve $G=0$ the family $P$ remains nonconstant as a polynomial family in $X$, since knowing the whole polynomial determines both $u,v$ and a curve cannot have both coordinates constant. Consequently $G\mid T_{x'}$ at no more than $d$ sites $x'$. At every other site at most $L\deg G$ of its initial pairs meet $T_{x'}=0$ by plane Bézout. If $c\le d$ sites contain the curve, counting agreements on this group bounds its size by $L\deg G\,(n-c)/(t-c)\le L\deg G\,(n-d)/(t-d)$. Summing over factors of $T_x$ bounds the number of regular candidates hitting this site by $L^2(n-d)/(t-d)$. A second count over the sites, again allowing at most $d$ identically constant ones, bounds the whole regular list by
$$
                         L^2\left(\frac{n-d}{t-d}\right)^2 .
$$

## Four exact boards

The table gives unrestricted closed-ball bounds at $n=2^{30}$ at either named prime, after identifying interleaved columns with scalar extension-field elements. Each row uses $r=16$. Reducing its agreement count by one removes its positive source surplus. The budgets include the singular solutions and first-order factors. They go beyond the named sponsor budgets; this calculation does not extend the integer thresholds for those budgets. [Finite comparisons](../../../scripts/probes/probe_second_order_linear_jet_board.py)

| Rate | $h_A,h_B$ | Safe errors at the displayed budget | Local rank | Source surplus | List budget |
|---|---|---:|---:|---:|---:|
| $1/2$ | $5,2$ | 324,179,110 | 951 | 234 | $2810n^2$ |
| $1/4$ | $8,5$ | 561,214,324 | 1402 | 4909 | $2289n^2$ |
| $1/8$ | $10,7$ | 723,318,701 | 1678 | 8267 | $1889n^2$ |
| $1/16$ | $11,8$ | 833,476,786 | 1815 | 721 | $1657n^2$ |
