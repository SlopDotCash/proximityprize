# Removing the intersection at infinity from the cubic bound

At the second production prime, with $n=2^{30}$ and code dimension $2^{26}$, every received pair has at most $2n$ MCA-bad scalars through **678536752 errors**. The resulting lower bound on the operational threshold is **678536753/1073741824**. The proof below is written mathematics. The accompanying program checks its finite inequalities in integer arithmetic.

## A projective resultant with its leading-coefficient factor removed

Give $X,Y,Z$ weights $1,d,0$. Let $F\in k[X,Z,Y]$ be primitive over $k[X]$ and irreducible over $k(X)$ in $Z,Y$, of weight $W$, positive $Y$-degree $b\ge2$ below the characteristic, and $Y$-leading coefficient $a(X,Z)$. Define
\[
 H(F)=F_{ZZ}F_Y^2-2F_{ZY}F_YF_Z+F_{YY}F_Z^2,\qquad L=3b-2.
\]
Assume $F\nmid H(F)$. Use the binary homogeneous resultant in $Y$ of $F,H(F)$ at the fixed respective degrees $b,L$, denoted by $R$. Its value is nonzero even if the actual degree of $H(F)$ drops, since $a\ne0$ over $k(X,Z)$.

Treat each $Y^i$ coefficient $c_i$ of $F$ and its first and second $Z$ derivatives as independent formal symbols of weight $W-id$. When $c_b=0$ the top $Y^L$ coefficient of $H(F)$ vanishes, since it equals
\[
 b^2 c_b^2 c_b''-b(b+1)c_b(c_b')^2.
\]
Both forms therefore vanish at $[1:0]$, and $c_b$ divides the universal resultant. Dividing in this universal ring and then evaluating shows that $R/a$ is a polynomial. Every term of the undivided Sylvester determinant selects $L$ coefficients of $F$ and $b$ coefficients of $H(F)$, with the selected $Y$ indices summing to $bL$. The coefficient at index $j$ of $H(F)$ has formal weight $3W-(j+2)d$. Consequently every surviving monomial of the quotient has formal weight
\[
 LW+3bW-(bL+2b)d-(W-bd)=(6b-3)W-(3b^2-b)d.
\]
After evaluation this bounds the $X$-degree of $R/a$, including cases where individual leading coefficients have less than their allowed degree.

The quotient still counts every finite received point with its full local intersection multiplicity. To verify this at an $X$-site where $a$ vanishes, use the chart $T=1/Y$ at infinity and put $S(T)=T^b F(1/T)$. In the function field of $S$, with prime denoting the derivative in $Z$ fixing $X$, one has $T'=-S_Z/S_T$, $T''=-H(S)/S_T^3$, and $F_Y(1/T)=-T^{2-b}S_T$. The implicit equation gives $H(F)(1/T)=-F_Y(1/T)^3(1/T)''$. Substitution yields the polynomial congruence
\[
 T^L H(F)(1/T) \equiv 2T S_T S_Z^2+T^2 H(S)\pmod S.
\]
Here $F$ has nonzero constant coefficient in $Y$ by irreducibility and $b\ge2$. Its reciprocal $S$ is irreducible and primitive over $k[X,Z]$, so the function-field identity clears to the displayed congruence in the polynomial ring.

Work over $k(Z)$, or its algebraic closure for intersection lengths. At $(X,T)=(x,0)$ the ideal of the two homogeneous forms is contained in $(S,T)$. Its intersection length is therefore at least the length of the quotient by $(S,T)$, which is $\operatorname{ord}_{X-x}a$ because $S(0)=a$. The local homogeneous resultant at $X=x$ counts all intersections in the projective $Y$ fiber, including this infinity point. This equality also follows by choosing a $Y$ chart over the local DVR with $F$ monic up to a unit and taking the determinant of multiplication by the dehomogenized $H(F)$ on the free algebra modulo $F$. Such a chart exists since primitivity over $k[X]$ gives $F(x,Z,Y)\ne0$. Hence every distinct finite received-point contribution survives dividing by $a$.

For the received line $Y=u(x)+Zv(x)$, let $\ell_x$ be the order of $F$ in the two translated local variables $X-x,Y-u(x)-Zv(x)$ over $k(Z)$. At sites with $\ell_x>0$, the order of $H(F)$ is at least $3\ell_x-2$: the expression commutes with translating $Y$ by this affine function of $Z$, and each $Y$ derivative loses at most one degree of local order. The local intersection is at least the product of the orders. Since $\ell(3\ell-2)\ge7\ell-6$ for every positive integer $\ell$, summing the finite contributions gives
\[
 \sum_{x}\ell_x\le
 \left\lfloor\frac{6n+(6b-3)W-(3b^2-b)d}{7}\right\rfloor.
\]
The local intersection inequality is property (5) of chapter 3, section 3 of Fulton's *Algebraic Curves*. [Author's text](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/fulton-curves.pdf)

## A second-prime certificate

Take $d=2^{26}-1$, $t=395205072$ agreements, $e=n-t$, and suppose $2n+1$ distinct bad scalars have been selected. Each scalar $z$ supplies a polynomial $q_z(X)$ of degree at most $d$ agreeing with the received fold at $t$ or more sites. Put
\[
 C(h,v,T)=\sum_{j=0}^{v}(h+1-j)\max(T-jd,0)
\]
for the displayed uses $v\le h$. The space of received-line interpolants of weight $<t$, total $(Z,Y)$-degree $\le h$ and $Y$-degree $\le v$ has dimension at least $C(h,v,t)-(h+1)n$. Every interpolant vanishes on each $(z,q_z(X))$ over $k(X)$.

The first interpolation at $(h,v)=(13,3)$ has surplus 30247654. The established linear and quadratic factor bounds at this agreement count force one irreducible cubic-in-$Y$ factor $F$. Each affine head accounts for at most $e+1$ labels, each remaining nonlinear factor of $Y$-degree one or two accounts for at most 4128, and $3(e+1)+3\cdot4128+13<2n$. The cubic therefore carries at least $M=2n+1-13$ of the chosen points. A second interpolation at $(7,5)$ has surplus 89756689. Since $M>13\cdot7$, Bézout forces this interpolant to be divisible by $F$, and $m=\deg_{Z,Y}F\le7$. If $m\le5$, the forward derivative bound for a moving cubic, summed with at most $13-m$ other labels, is already less than $2n$. Its identically zero alternative gives only a head or a small set. For the rest take $m=6$ or $7$. The identically zero reverse derivative $F\mid H(F)$ gives at most three points on this irreducible cubic by its splitting into geometric lines. [Low-degree factors](second-prime-quadratic-discriminant.md) · [Forward derivative](second-prime-moving-cubic.md) · [Identically zero reverse derivative](second-prime-quartic-intrinsic.md)

At $h=300000000$, all $(h,5)$ interpolants are divisible by $F$ since $7h<M$. Their dimension is at least $87256696953767048$. If $W\ge231144322$, their quotients have total degree at most $h-6$, $Y$-degree at most two and weight below $t-231144322$. They would have dimension at most $87256696689083760$, a contradiction. The preceding resultant bound gives
\[
 W\le231144321,\qquad \deg_X(R/a)\le1856552103,\qquad R_0:=\sum_x\ell_x\le1185571863 .
\]

Use the polynomial-multiplier jet argument at $\mu=4129$, $s=715827875$ with auxiliary monomials having $Y$-degree at most two, total $(Z,Y)$-degree at most $s$, and weight below $\mu t$. The codimension of the local multiple-of-$F$ condition at $x$ over $k(Z)$ is $w_x=\mu\ell_x-\binom{\ell_x}{2}$, so $\sum_x w_x\le(\mu-1)R_0+n\le4895114392288$. At each site there are $A=\binom{\mu+1}{2}$ jet entries; selecting independent multiples of the jet of $F$ spanning its image and giving their scalar-polynomial coefficients degree at most $s-7$ makes the net cost at most $(s+1-7)w_x+7A$. The equations hold as polynomial identities, including all their specializations. The difference between the number of auxiliary-polynomial coefficients and the total net cost is at least $15729676125399$. There is a nonzero auxiliary polynomial $P$ of smaller $Y$-degree than $F$. It vanishes identically on all $M$ chosen points of $F$ by the $t$ agreements of multiplicity $\mu$ and the strict weight bound. The nonzero $Y$-resultant with $F$ has scalar degree at most $3s+2(7-3)=2147483633<M$. This contradiction proves goodness at $e=678536752$. Constancy between successive Hamming radii gives the stated threshold lower bound. The three-head upper endpoint remains $715827882/n$. [Polynomial-multiplier jet proof](second-prime-intrinsic-cubic.md) · [Exact arithmetic](../../../scripts/probes/probe_second_prime_normalized_hessian.py)
