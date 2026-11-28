# Sharper collision multiplicities for the first-prime eighth-rate list

Agreement $s=171/500$ suffices for the first named eighth-rate list budget on every injective grid of length $n=2^{30}$ and at every positive interleaving width. This proves safety through **706,522,120 errors**, raising the first-failure lower bound to **706,522,121**. The exact threshold remains open. The improvement uses how a rational differential equation restricts the slopes of two words through the same point. [Previous coupled estimate](eighth-list-coupled-cofactor.md) · [Exact verifier](../../../scripts/probes/probe_eighth_collision_multiplicities.py)

The quartic primary, adaptive comparisons and individual exterior-word proof from the preceding result hold at the new agreement. For the remaining degree-six linear factor $A(X,Y)+B(X,Y)V$, the exterior comparison leaves at least $M=n-1000$ sections in an oversized list. The same plane intersection calculation allows excess $nJ$ with $J=104/1000$. Put $d=n/8-1$, $R=d/n$. Write $p_x$ for the fraction of these sections agreeing with the center at $x$, and $\mu=n^{-1}\sum_xp_x$. We have $s\le\mu\le\sqrt{R+1/M}$. For an exceptional class $C$ write $q_C$ for its section frequency. [Intersection reserve and cofactor rank](quarter-list-darboux-cofactors.md#exceptional-collision-classes)

## Classifying collisions away from the received ordinates

The classes of type $T$ consist of exceptional slopes through a physical received ordinate. All other collisions of at least two sections occur at common zeros of $A,B$ away from the received point, including other ordinates above a physical abscissa. At such a zero $(x,y)$, compare the linear Taylor terms along $Y=y+v(X-x)+\cdots$. Every realized slope $v$ satisfies
$$
 A_X+(A_Y+B_X)v+B_Yv^2=0 .
$$
If this polynomial is nonzero, call the point type $N$. Its sections use at most two slopes. Every pair of sections with a common slope contributes a second root multiplicity to their difference.

If this polynomial vanishes identically and $B_X\ne0$, call the point type $S$. Set $U=X-x$ and $Y=y+Uz$. The linear terms of $A,B$ are $-B_X(Y-y), B_XU$. Thus $(A+zB)/U^2$ and $B/U$ are regular after substitution, with the latter a unit at every finite slope over $U=0$. The transformed equation
$$
 (A+zB)/U^2+(B/U)z'=0
$$
is regular there. If two distinct sections have the same $z(0)$, the equation makes the derivative of their difference divisible by that difference in the local power series ring. Its positive order is less than the characteristic, so differentiation lowers its order by one, a contradiction. Every pair through this point therefore has distinct slopes and meets simply. Their logarithmic residue row is the same class indicator, with sign $-1$, for every anchor through the point once the anchor columns have been set aside. At all remaining points of type $H$ all first derivatives of $A,B$ vanish. The intersection multiplicity of these two coprime plane curves there is at least four.

Charge $w_C=2$ units of excess to a type $H$ class, and one otherwise. The physical tangent reserve and these disjoint point charges give $\sum_C w_C\le nJ$. In the pair count use $\kappa_C=3/2$ for type $N$, and one otherwise. In type $N$ with slope frequencies $q_1,q_2$ the common slope pairs restore $q_1^2+q_2^2\ge q_C^2/2$ before removing diagonals. A pair pays separately for each common true hit, for extra multiplicity in a shared type $T$ slope, and for its multiplicities at all nonreceived ordinates. Restoring diagonals costs at most $n(1+2J)/M$, allowing two per nonreceived class. Consequently
$$
 n^{-1}\sum_C\kappa_Cq_C^2\le C_0-\mu^2,\qquad C_0=R+(1+2J)/M .
$$

## Counting the actual residue rows

Choose five distinct random anchors. Set $F(u)=1-(1-u)^5$ and $u_T=n^{-1}\sum_{C\in T}q_C$. At a physical abscissa the common true-hit row is needed only if some anchor has a nonexceptional true hit. When every hitting anchor lies in an exceptional slope class, count the actual residue row for each such anchor directly. Under independent sampling the expected common-row fraction is at most $F(\mu-u_T)$ by Jensen. Concavity bounds this by $F(\mu)-5(1-\mu)^4u_T$. Including the $5nu_T$ exceptional incidences leaves coefficient $5[1-(1-\mu)^4]$ on the total type $T$ mass.

For types $N,H$ count each anchor visit. For a type $S$ point one row suffices for every visit, so the expected contribution is $F(q_C)$. Conditioning on distinct anchors changes each union-event probability by at most $10/M$, the repeated-draw probability. Incidence expectations are exact for either sampling rule. The aggregate correction normalized by $n$ is at most $10(1+J)/M$ for the physical sites and type $S$ points together.

Take $\beta=83/100$ and $c=21/1000$. On the feasible range $1-(1-\mu)^4\le\beta$. The tangent to $F$ at $46/1000$ gives $F(q)\le5\beta q+c$ on $[0,1]$. After extracting $cnJ$, the coefficients of each $5q_C$ are bounded by $\beta\sqrt{w_C\kappa_C}$ for every type. Indeed $\beta^2\ge2/3$ for type $N$, and $\beta^2\ge1/2$ for type $H$. Cauchy–Schwarz now bounds the cofactor rank by
$$
 6+n\left[F(\mu)+5\beta\sqrt{J(C_0-\mu^2)}+cJ+10(1+J)/M\right].
$$
The variable part is concave and has nonpositive derivative at $s$ because $(1-s)^8(C_0-s^2)\le\beta^2Js^2$. Its value at $s$ gives rank at most **1,072,464,183**. The resulting nullity is at least **1,276,641**, forcing a primitive first integral of ordinate degree at most **841**. The tame split-fiber and stationary-branch Riccati bounds from the previous proof exclude it. The verifier checks the interpolation, both numerical tangent bounds and the final split-fiber comparisons. [First integrals and moving branch labels](quarter-list-darboux-cofactors.md#from-cofactor-relations-to-completely-split-fibers)

```sh
python3 scripts/probes/probe_eighth_collision_multiplicities.py
```
