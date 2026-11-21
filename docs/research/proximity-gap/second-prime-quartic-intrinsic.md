# No irreducible quartic at the last second-prime predecessor

Let $k$ be the algebraic closure of the second production prime field, $K=k(X)$, $n=2^{30}$, $d=2^{26}-1$, and $t=(n-1)/3+2=357913943$. Each of $2n+1$ distinct scalar labels $z$ selects a polynomial $q_z\in k[X]$ of degree at most $d$ agreeing with $L_x(z)=u(x)+zv(x)$ on at least $t$ of $n$ distinct evaluation sites $x$. The first-order interpolation theorem gives a nonzero polynomial vanishing on all the points $(z,q_z)\in K^2$, of total $(Z,Y)$-degree at most 34 and $Y$-degree at most four. We prove that this polynomial cannot have an irreducible factor of $Y$-degree four. The conclusion concerns the factor over $K$, without a geometric irreducibility assumption.

Suppose $F$ is such a factor, chosen primitive over $k[X]$. Write $m=\deg_{Z,Y}F$, so $4\le m\le34$. All remaining factors depend only on $Z$ over $K$, and their product has at most 34 scalar roots. At least $M=2n+1-34=2147483615$ of the chosen points therefore lie on $F$.

## The entire interpolation space bounds the weight of the factor

Give $X,Y,Z$ weights $1,d,0$. The number of monomials of total $(Z,Y)$-degree at most $h$ and weight strictly below $v$ is
\[
 D(h,v)=\sum_{j=0}^{h}(h-j+1)\max(v-jd,0).
\]
Imposing $Q(x,Z,L_x(Z))=0$ costs at most $h+1$ linear conditions per site. Every resulting $Q$ vanishes on every selected point because $Q(X,z,q_z(X))$ has degree below $t$ and at least $t$ distinct roots. At $h=119$ the entire space has dimension at least $D(119,t)-120n=6375345000$. Every nonzero member is divisible by $F$ over $K$ by plane Bézout, since $M>119\cdot34$. Gauss's lemma gives a quotient in $k[X,Z,Y]$. Both total degree and weight are additive under products, using the domain property of the highest homogeneous parts. If $W$ is the weight of $F$, the quotients all have total degree at most 115 and weight strictly below $t-W$. The two consecutive capacities are
\[
 D(115,t-302954072)=6375345036,\qquad
 D(115,t-302954073)=6375344920.
\]
Hence $4d\le W\le302954072$.

## Multiplicities over the scalar function field

Work also over $k(Z)$ in the variables $X,Y$. Primitivity and irreducibility imply that $F$ remains irreducible there. Indeed a factor over $k(Z)[X,Y]$ clears to a factor over $k[Z,X,Y]$, as $F$ is primitive over $k[Z]$. Set
\[
 N=F_{ZZ}F_Y^2-2F_{ZY}F_YF_Z+F_{YY}F_Z^2.
\]
Its $Y$-degree is at most 10 and its weight is at most $3W-2d$.

First consider $F\mid N$. The root $y$ of $F$ is separable over $K(Z)$ because its degree is $4<p$. In its function field with $X$ fixed, implicit differentiation gives $y''=0$, so $c_1=y'=-F_Z/F_Y$ and $c_0=y-Zy'$ have derivative zero. They are algebraic over $K$. To see this last point, write each as $A/B$ with $B=F_Y$, $Y$-degrees at most four and $Z$-degrees at most $m+1$. The nonzero resultant $\operatorname{Res}_Y(F,A-CB)$ has $Z$-degree at most $4(m+1)+4m<p$. The primitive minimal-polynomial factor for $C=c_i$ inherits that degree bound. After making it monic, differentiation at $c_i$ shows that its differentiated coefficient polynomial of smaller $C$-degree vanishes identically. Every coefficient belongs to $K(Z^p)$, the derivative kernel. A reduced ratio of $Z$-degree below $p$ in that kernel belongs to $K$. This proves the claim. Consequently over $\bar K$ the irreducible factor $F$ splits into lines $Y=c_0+c_1Z$ up to a unit. Indeed its conjugate monic product has coefficients polynomial in $Z$ and in $K(Z)$, hence in $K[Z]$, and $F$ is primitive over $K[Z]$. Two distinct selected $K$-points on the same such line would solve for $c_0,c_1\in K$, giving a linear factor over $K$. This bounds $M$ by four, a contradiction.

Assume now $F\nmid N$. If $b'$ is the actual $Y$-degree of $N$, its nonzero $Y$-resultant with $F$ over $k(Z)[X]$ has $X$-degree at most
\[
 b' W+4(3W-2d)-4b'd\le22W-48d\le H=3443764160.
\]
A Sylvester term uses $b'$ coefficients of $F$ and four of $N$ whose $Y$-indices sum to $4b'$. This proves the first bound. The middle inequality uses $b'\le10$ and $W\ge4d$.

At site $x$ put $r_x=\operatorname{ord}_{(T,V)}F(x+T,Z,L_x(Z)+V)$ in the polynomial ring over $k(Z)$. Primitivity over $k[X]$ makes $F(x,Z,Y)$ nonzero, so $0\le r_x\le4$. The sites with $r_x>0$ will be called identity sites. The formula for $N$ commutes with $Y\mapsto Y+L_x(Z)$ since $L_x''=0$, by expanding the three differentiated terms. Coefficient differentiation in $Z$ preserves the $(T,V)$-order, and every $V$-derivative loses at most one. Thus $N$ has order at least $3r_x-2$ at every identity site. The proper intersection multiplicity there is at least $r_x(3r_x-2)\ge7r_x-6$. The sum of these local intersection numbers is at most the $X$-degree of the resultant. This follows, for example, by homogenizing in $Y$ at the actual $Y$-degrees and taking the local resultant over each DVR $k(Z)[X]_{(X-x)}$. Its valuation counts the intersections in that projective fiber including infinity. The primitive $F$ does not contain any such fiber, and coprimality gives a finite intersection scheme. Summing over identity sites gives
\[
 R=\sum_x r_x\le\left\lfloor(6n+H)/7\right\rfloor=1412316443.
\]
The local inequality used here is the multiplicity bound in William Fulton's *Algebraic Curves*, chapter 3, section 3, property (5). [Author's text](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/fulton-curves.pdf)

## An auxiliary polynomial on the quartic

Choose $\mu=64$, $s=67108864$, $E=524288$, and $A=\binom{\mu+1}{2}=2080$. Use the unknown monomials $X^a Z^iY^j$ with $0\le j\le3$, $0\le i\le s-j$, and $0\le a<\mu(t-E)-jd$. Their number is
\[
 C=\sum_{j=0}^3 (s-j+1)(\mu(t-E)-jd)=6112885878044316792.
\]
At an identity site $x$, use the truncated jet algebra $k(Z)[T,V]/(T,V)^\mu$, of dimension $A$. Require the translated class of the unknown polynomial $P$ to lie in the ideal generated by the translated $F$. Multiplication by $F$ has rank $\binom{\mu-r_x+1}{2}$ since multiplication by its lowest homogeneous part is injective on every graded piece below degree $\mu-r_x$. The codimension is $\mu r_x-\binom{r_x}{2}\le\mu r_x$. The matrix entries have $Z$-degree at most $m$, and the translated $P$ entries have $Z$-degree at most $s$. Fix a nonzero maximal rank minor. For each remaining row the augmented determinant must vanish identically. This gives at most $(s+mA+1)\mu r_x$ scalar linear constraints. When the pivot remains nonzero after specialization, these equations imply membership in the specialized ideal. The total number of scalar conditions is at most
\[
 \mu R(s+34 A+1)=6072245281882633920<C.
\]
Take a nonzero solution $P$. Its $Y$-degree is at most three, so it is coprime to $F$ over $K(Z)$.

At each identity site the pivot vanishes for at most $mA$ labels. At any other site $F(x,Z,L_x(Z))$ is a nonzero polynomial of degree at most $m$, so there are at most $m$ agreements from the selected labels on $F$. Thus the loss of valid agreements, summed over all labels, is at most $34(A+1)n$. At most $\lfloor34(A+1)n/(E+1)\rfloor=144903915$ labels lose more than $E$ agreements. Every remaining label on $F$ has at least $t-E$ sites with specialized jet membership. At each such $x$, substitute $V=q_z(X)-L_x(z)$ and $T=X-x$. The ideal $(T,V)^\mu$ maps into $((X-x)^\mu)$, and $F(X,z,q_z(X))=0$. Hence $P(X,z,q_z(X))$ vanishes to order at least $\mu$ there. Its degree is strictly below $\mu(t-E)$, so it vanishes identically. At least $M-144903915=2002579700$ scalar labels therefore give common roots of $F,P$.

Finally $\operatorname{Res}_Y(F,P)\in K[Z]$ is nonzero and has degree at most $4s+3(m-4)\le268435546$. This is the same Sylvester index sum, with total $(Z,Y)$-degree in place of weight. Every counted scalar annihilates the resultant, also when a specialized degree drops. The strict inequality $2002579700>268435546$ proves the contradiction.

The elimination is a written proof. The integer certificate checks the dimension bounds and all strict inequalities. [Exact arithmetic](../../../scripts/probes/probe_second_prime_intrinsic_quartic.py)
