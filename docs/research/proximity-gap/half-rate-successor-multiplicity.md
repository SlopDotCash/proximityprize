# A universal half-rate MCA bound one step past unique decoding

For $h=2^{28}$ and $n=4h$, set $d=2h-1$. On **every** injective length-$n$ evaluation domain in either named prime field, any two received rows have at most **$4(e+1)$** MCA-bad scalars whenever $h+1\le e\le269812048$. Thus the second named prime meets its budget $2n$ through **269,812,048 errors**, and its operational supremum is at least **$269812049/n$**. At the first successor $e=h+1$ the stronger bound **$n+3$** leaves the first named prime within three labels of its budget. Write $e=h+a$, $t=3h-a$ below, with $1\le a\le1376592$. This is a written proof. [Reverse Hessian and zero case](second-prime-quartic-intrinsic.md)

Put $k=\overline{\mathbf F}_p$. Write $X$ for the evaluation coordinate, $Z$ for the scalar and $Y$ for the value. We give $X,Z,Y$ weights $1,0,d$ respectively. A bad scalar $z$ supplies a polynomial $q_z(X)$ of degree at most $d$ agreeing with the received line $L_x(z)$ at $t$ or more sites $x$. Its actual witness excludes a joint explanation on those sites.

## A quartic containing every selected point

Seek $Q(X,Z,Y)$ of value degree at most four, total $(Z,Y)$ degree at most $s$, and weight strictly less than $T=3t=9h-3a$. At each site require order at least three in $(X-x,Y-L_x(Z))$. The terms of order $i+j<3$ in the translated polynomial have scalar degree at most $s-j$, costing at most $6(s+1)-4$ scalar conditions per site. The variables number $\sum_{j=0}^4(s-j+1)(T-jd)=(s+1)(25h+10-15a)-30h+30a-30$. The dimension is therefore at least

\[
 (s+1)(h+10-15a)-14h+30a-30.
\]

At $s=14$ this is $h-195a+120>0$. Every such polynomial vanishes on every chosen point $(z,q_z(X))$ over $k(X)$, since substitution gives a univariate polynomial of degree below $3t$ with $t$ roots of multiplicity at least three. Fix a nonzero $Q_{14}$ and divide out any factors $Z-z$. These are units over $k(Z)$, so the translated jet identities still hold identically after division, including at their specializations. Thus every selected point lies on a positive-value-degree factor. A factor independent of $Y$ accepting a selected scalar would be divisible by $Z-z$ over $k[X,Z]$.

Suppose a positive-value-degree irreducible factor $F$ of $Q_{14}$ carries more than $14s$ labels for $s=10^6$. Choose its primitive representative in $k[X,Z,Y]$; write $b=\deg_Y F$, $W=\mathrm{wt}(F)\ge bd$. Every member of the larger interpolation space is divisible by $F$ by plane Bézout over $k(X)$, since $14s$ bounds the number of shared points of coprime polynomials of those degrees. Gauss's lemma gives polynomial quotients. Passing to $K=k(Z)$, write $i_x$ for the order of $F$ at $(x,L_x)$ in the variables $X,Y$. Irreducibility gives $i_x\le b$: at the fixed $x$ the entire value polynomial cannot vanish. The residual polynomials $R$ have value degree at most $4-b$, weight less than $L=T-W$, and order at least $(3-i_x)_+$ at every received site. Their $K$-span has dimension at least $h-B$ with $B=20652700$. Use $C=23406000$ as a uniform slack. In the estimates below it includes the cost of up to two agreement losses beyond $h$, since $B+2a\le C$. Indeed, projecting the coefficient vectors of the original interpolation polynomials in $(X,Y)$ onto a maximal independent set of coordinate slots is injective over $K$. Each projected slot has at most $s+1$ scalar coefficients over $k$. Thus the rank is at least $h+10-15a-14h/(s+1)>h-B$. Division by $F$ preserves that rank. We can enlarge the space to all residuals with those degree and order constraints.

The interpolation is now kernel checked on the actual domain and arbitrary received rows. Lean produces a nonzero supported trivariate polynomial at $t=803929776$, proves its specialization vanishes for every polynomial with that many agreements, and gives the lower bound $247782756\cdot1000001$ for the base-field dimension at the larger cutoff. The residual-module and factor exclusions below remain written proofs. [Lean interpolation and dimension bounds](../../../ArkLib/Research/ProximityGap/Frontier/HalfSuccessorJetInterpolation.lean)

## Two estimates for the residual space

Use the polynomial module in $K[X]^{q+1}$ for value degree at most $q$, with coefficient in slot $j$ shifted by $jd$. It consists of all polynomials meeting the specified local orders without a weight cutoff. Choose one minimal shifted-weight element $R_j$ at each leading position, breaking weight ties by value index. All positions occur because a fixed product of site factors kills the jets. Cancelling the leading monomial gives a basis over $K[X]$, and truncation to weight $<L$ has dimension $\sum_j(L-w_j)_+$, where $w_j$ are the basis weights. Distinct leading positions also give independence over $K(X)$. When all $q+1$ basis elements occur below the cutoff the dimension equals the dimension of the unrestricted slots minus the colength of the jet constraints. To see this, compare at a sufficiently high cutoff: at different sites arbitrary coefficient jets can be assigned independently by the Chinese remainder theorem. Subtracting the colength there determines $\sum w_j$ and hence the dimension at every cutoff above every basis weight.

If only one basis direction occurs, write its representative $G$ after removing the common $K[X]$-factor of its value coefficients. This includes $G=1$. Every available residual is a polynomial-in-$X$ multiple of $G$. With $g=\mathrm{wt}(G)$ and $j_x=\operatorname{ord}_{(x,L_x)}G$, those multiples must supply a coordinate factor of degree at least $u=\sum_x(3-i_x-j_x)_+$. The dimension bound therefore implies

\[
 W+g+u\le8h+B. \tag{1}
\]

Any primitive positive-value-degree factor common to the available residuals divides $Q_{14}/F$, which is itself an available residual. Clearing scalar denominators yields a factor of total $(Z,Y)$ degree at most 14 by Gauss's lemma. For such a factor $G$ distinct from $F$, there is a selected $q_z$ on $F$ that does not belong to $G$, by Bézout, even after excluding a second factor. Then at its agreement sites $I$ one has $\sum_{x\in I}j_x\le g$ since $G(X,z,q_z)$ has degree at most $g$. Local order inequalities are polynomial identities in $Z$ and persist at specialization. In particular for a primitive linear $G$ one has $j_x\in\{0,1\}$ and $\sum j_x\le g+e$.

For $2\le b\le4$ use $N=F_{ZZ}F_Y^2-2F_{ZY}F_ZF_Y+F_{YY}F_Z^2$. If $F\mid N$, the degree-below-characteristic geometric-line argument gives at most $b$ selected points. Otherwise the nonzero value resultant has coordinate degree at most $H_b=(6b-2)W-3b^2d$ by its Sylvester index sum. The Hessian commutes with affine received-line translation and has order at least $3i_x-2$ at every site of positive order. Proper local intersection multiplicity is at least the product of the two local orders. Hence

\[
 \sum_x i_x(3i_x-2)\le H_b. \tag{2}
\]

This use of the homogeneous resultant allows degree drops upon specialization. The primitive first curve has no vertical component. The characteristic requirements for the geometric-line argument hold in both fields: its scalar minimal-polynomial height is at most $b(14+1)+b\cdot14<p$. [Full local argument](second-prime-quartic-intrinsic.md)

## Excluding value degrees four and three

At $b=4$, (1) applies with $G=1$, and $u\le C+4$ since $W\ge4d$. At all other sites $i_x\ge3$. Thus $84h-21(C+4)\le H_4\le80h+22C+48$, impossible.

At $b=3$ a linear residual $AY+B$ must have both coefficients divisible by the product of $(X-x)^{(2-i_x)_+}$, of degree $u$. After removing it, there is one linear condition $B(x)+A(x)L_x=0$ at each of the $v=\#\{i_x<3\}$ sites. If two basis directions occur, the colength count gives $h-C\le 2(L-u)-d-v$, so $2W+2u+v\le15h+C+1$. For $i=0,1,2,3$ the loss from 21 in $i(3i-2)$ is at most $13[2(2-i)_++\mathbf1_{i<3}]$. Equations (2) and $H_3=16W-27d$ give $10W\le57h+13C+40$, inconsistent with $W\ge3d$.

If only one direction occurs and $G$ is linear, (1) and $\sum j_x\le g+e$ give $\sum i_x\ge W+3h-C-1$, with $W\le6h+C+1$. As $i(3i-2)\ge13i-18$, (2) gives $3W\ge21h-13C-40$, impossible. If $G=1$ the same calculation uses $\sum i_x\ge W+4h-C$ and $W\le8h+C$, again impossible.

## Excluding value degree two

Write $n_i=\#\{x:i_x=i\}$. Here (2) gives both $32h-8n_0-7n_1\le10W-12d$ and $7\sum i_x\le10W+12$.

If three residual basis directions occur, the colength at a site is $\binom{4-i_x}{2}$ since the required order is $3-i_x\le3$ and all the required value-derivative slots exist. The global colength is $4h+5n_0+2n_1$. From the dimension $3L-3d-(4h+5n_0+2n_1)$ we obtain $3W+5n_0+2n_1\le16h+C+3$. Since $8n_0+7n_1\le(7/2)(5n_0+2n_1)$, the Hessian inequality gives $W\le7C+45$, whereas $W\ge2d$.

If two directions occur, take their basis polynomials $R_1,R_2$, of weights $w_1,w_2$ with $w_1+w_2\le17h-2W+B$ from the truncated dimension. If both are value-linear or constant, the linear-slot module containing them has both independent directions below the cutoff. Dividing out the forced site factors of degree $u=\sum(2-i_x)=8h-\sum i_x$, it has one further condition at each of the $4h$ sites. Thus $h-C\le2(L-u)-d-4h$, giving $2W+2u\le11h+C+1$. Together with $7(8h-u)\le10W+12$, this forces $h\le5C+17$.

Assume at least one $R_i$ is a quadratic. First suppose they have no common positive-value-degree factor. Remove their common horizontal factor of degree $v$ and let $a_x$ be its order at $x$. The resulting polynomials have no common component, so local intersection and their value resultant give

\[
 4v+\sum_x(3-i_x-a_x)_+^2\le 2(w_1+w_2)-4d\le26h-4W+2C+4.
\]

Indeed at least one has value degree two; raising the degree bound of the other up to two in the Sylvester index sum is legitimate since the quadratic's weight after division is at least $2d$. This inequality also covers a value-constant residual: its nonzero resultant with the other polynomial counts intersection with the vertical fibers of the constant polynomial. At a site, minimizing $4a+(3-i-a)_+^2$ over integers $a\ge0$ gives respectively $8,4,1$ for $i=0,1,2$. Thus $7n_0+3n_1\le22h-4W+2C+4$. Since $8n_0+7n_1\le(7/3)(7n_0+3n_1)$, (2) then implies $2W\ge14h-14C-64$, while $4W\le22h+2C+4$.

If the two independent residuals share a primitive positive-value-degree factor $G$, its value degree is one. After dividing by $G$ and their common horizontal factor of degree $v$, the two coprime residuals are value-linear or constant, one of them linear. The same resultant bound with degrees one gives

\[
 2v+\sum_x(3-i_x-j_x-a_x)_+^2\le w_1+w_2-2g-d\le15h-2W-2g+C+1.
\]

The left hand side is at least $\sum_x(3-i_x-j_x)$. From $\sum j_x\le g+e$ and $g\ge d$ we get $\sum i_x\ge2W-2h-C-3$. The Hessian inequality now gives $4W\le14h+7C+33$, again inconsistent with $W\ge2d$.

If only one residual direction occurs, use (1). For $G=1$ one gets $\sum i_x\ge W+4h-C$ and $W\le8h+C$. For linear $G$ one gets $\sum i_x\ge W+3h-C-1$ and $W\le6h+C+1$. Either contradicts $7\sum i_x\le10W+12$ at the stated $h$. If $G$ factors into two linear factors, count the linear multiplicities separately, allowing a repeat. A selected scalar outside both factors gives $\sum j_x\le g+2e$. Then $\sum i_x\ge W+2h-C-2$, whereas $W\le4h+C+2$, which gives the same contradiction.

It remains for $G$ to be an irreducible quadratic. Both heights are at most $4h+C+2$, and $u\le C+4$. If $G$ is associated to $F$, at least $4h-u$ sites have $i_x=2$; (2) is immediately violated. Otherwise choose a selected section on $F$ outside $G$. At most $u$ sites have $i_x=0$ or $j_x=0$, and at most $u$ have $i_x\le1$ and $j_x\le1$, by the definition of $u$. Thus at least $4h-n_2-u$ sites have $j_x=2$. On the agreement set of the selected section the sum of the $j_x$ is at least $6h-n_2-2u-2a$, and at most $g$. Use $u\le B+4$, $g\le4h+B+2$ and $B+2a\le C$. Consequently $n_2\ge6h-2u-2a-g$. The Hessian lower bound $4h-n_0+7n_2\le10W-12d$ and $n_0\le u$ give $70h-12-14a\le10W+7g+15u$. But (1) and $W,g\ge2d$ bound the right hand side by $68h+15B+26$. This would require $2h\le15B+14a+38$, impossible throughout the stated interval.

## Counting the heads

For an irreducible value-linear factor carrying more than $14\cdot10^6$ points, the usual identity-site argument makes it an affine head. Explicitly, let $U$ consist of sites where its substitution at $Y=L_x(Z)$ vanishes identically. Other sites match at most 14 of these scalars. Thus $|U|\ge t-14n/(14\cdot10^6)$. On $U$ the coefficient of $Y$ is a nonzero polynomial of degree at most 14 in $Z$, so at most 14 selected sections fail to equal the received fold at any such site. The fifteen sections with fewest misses on $U$ each miss at most $14n/(14\cdot10^6-14)$ sites. Any three therefore share more than $d$ sites and lie on a common affine secant $q_z=A+zB$. The fifteen points force divisibility by that line as the total degree is at most 14. A head carries at most $e+1$ actual bad labels. Indeed if its joint core has size $c$, each of its $L_0$ labels needs at least $\max(1,t-c)$ distinct fresh sites, and outside the core at most one scalar can agree at each site. This gives $L_0\max(1,t-c)\le n-c$.

All other factors carry fewer than $e+1$ labels. Therefore the at most four factors altogether carry at most $4(e+1)$ labels. At $e=269812048$ this is $1079248196<2n$.

Specialize now to $a=1$. If there are more than $n$ bad labels, the four-factor allowance and $3(h+2)+14\cdot10^6<n$ force four distinct affine heads covering all labelled points. Each carries at least $h-5$ labels and consequently has core size at least $t-1=3h-2$. Three noncollinear heads have nonzero coordinate determinant of degree at most $2d$. At a site in $v$ of their cores the determinant is divisible by $(X-x)^{v-1}$ by subtracting coincident rows. Hence the three cores would cover at least $3(3h-2)-2d=5h-4>n$ sites. All four heads are therefore collinear over $k(X)$.

Write the heads as $(A,B)+D_i(X)(S(X),T_1(X))$ with $S,T_1$ coprime. The scalars $D_i$ are polynomials since a polynomial Bézout combination of $S,T_1$ is 1. Put $m=\max(\deg S,\deg T_1)$, so $\deg(D_i-D_j)\le d-m$ for each distinct pair. Let $b_0$ be the number of sites uncovered by all four cores. Each pair of cores meets on at least $2(3h-2)-(4h-b_0)=2h-4+b_0$ sites, all roots of $D_i-D_j$. Thus $b_0\le3-m$. Each covered site gives at most one fresh scalar across all the heads, as distinct evaluated head pairs lie on the same line through the received pair. If $m=0$ this direction is constant across all covered sites, giving at most one fresh label there and at most $4b_0$ elsewhere. If $m\ge1$ then $b_0\le2$. Equality would force $m=1$, every core of size $3h-2$ and every pair union equal to the entire covered set. Every covered site would then belong to at least three cores, impossible since $4(3h-2)<3(4h-2)$. Thus $b_0\le1$ and the total number of fresh labels is at most $(n-b_0)+4b_0\le n+3$.

For the first named prime, any failure at this step requires precisely one uncovered site and $m=1$. Indeed $m=2,b_0=1$ again would force every pair union to be the whole covered set and every core to have size $3h-2$, violating $4(3h-2)<3(4h-1)$. Its budget is $n$; the remaining difference is at most three labels. The second named budget $2n$ exceeds the unconditional bound throughout the stated interval. Monotonicity and constancy between consecutive Hamming steps give the stated lower bound on its operational supremum. [Canonical MCA event and radius](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean)

The integer certificate verifies all strict production inequalities, the interpolation dimension counts and the finite local deficit inequalities. [Exact numerical checker](../../../scripts/probes/probe_half_rate_successor_multiplicity.py)
