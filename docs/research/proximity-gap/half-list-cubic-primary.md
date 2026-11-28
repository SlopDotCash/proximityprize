# A half-rate list bound at 88/125 agreement

Let $n$ be a positive integer and $K$ a field of characteristic zero or characteristic $p>20000$. On any $n$ distinct elements of $K$, every received word agrees on at least $88n/125$ sites with at most **1,800,018** polynomial words of degree at most $n/2$. This holds at every positive interleaving width. In particular both designated fields at length $2^{30}$ meet their list budgets through **317,827,579 errors**. The previous bound of 1,200,018 at the higher agreement $1411/2000$ remains available. [Exact verifier](../../../scripts/probes/probe_half_cubic_uniform.py) · [Previous bounds and local inequalities](half-list-joint-occupancy.md)

## A normalized adaptive interpolation

Set $R=1/2$, $s=88/125$, $L=600000$. Use weights $1/n,R,R$ on $X,Y,V$, and the source $S$ and local rank $C$ of the uniform proof. Finite lists suffice. Scalarize using an indeterminate and pass to the algebraic closure. The order-13 primary equation of derivative degree at most three exists because $S(13s,3)-C(13,3)=16/25>0$. It captures every candidate jet and its generic total degree is at most $b_0=18$. Derivative-independent factors account for at most $b_0$ words. It suffices to exclude $L$ words assigned to any one irreducible factor $g$ of positive derivative degree $v$. Write $D$ for its normalized weight. [Uniform source difference and capture](half-list-uniform-length.md#a-source-bound-uniform-in-the-length)

Suppose $v=2$ or $3$. Delete at most $b_0^2$ words meeting $g_V=0$ over the generic point. From each remaining word choose hit weights $u_{i,x}$ between zero and one with sum $sn$. Write $p_x$ for their average in the group, $z$ for its variance and $M_0=L-b_0^2$. Distinct words have at most $Rn$ common hits while each diagonal contributes at most $sn$. Thus $z\le V=R-s^2+(s-R)/M_0$. For each word, $n^{-1}\sum_x u_{i,x}p_x\le R+(s-R)/M_0$. If $o_x$ is the radial order of $g$, evaluation of $g_V$ gives $\mathbb E(p_x o_x)\le s+D-R$, and primitivity gives $o_x\le D/R+v$. [Radial order and occupancy bounds](sixteenth-list-joint-quotient.md#one-assignment-of-multiplicities-for-all-large-groups)

Set $r=2000$, $h=300$, $\lambda=2600$ and $q_x=\lfloor r+\lambda(p_x-s)\rfloor$. The average of $n^{-1}\sum_x u_{i,x}q_x$ over retained words is at least $(r-1)s+\lambda z$. The upper bound for each individual word is $rs+\lambda V$. Hence at least $2M_0s/(3s+\lambda V)$ words have weighted agreement at least $nw$, where $w=(r-3)s+\lambda z$. Fractional selection only decreases the multiplicity counted on actual hits. The strict normalized weight cutoff $w$ is valid for every $n$.

Write $B(q)=C(q,h)-C(q,h-v)$, $J(q)=C(q,h-v)-C(q-1,h-v)$, and $c=J(r)/s$. For $q=q_x$, put $a=q-r$ and $\Delta=(r\min(|a|,|a+1|)/\lambda)^2$. The verifier checks the two scalar inequalities
$$
 B(q)\le B(r)+u a+r/2+b_2\Delta,\qquad
 J(q)\le J(r)+c a/\lambda+r/2+j_2\Delta
$$
at every possible integer $q$, where $u=[B(r+8)-B(r-8)]/16>0$. Use $b_2=1.692,2.539$ in order of $v$ and $j_2=0.015$ for both. Since $\Delta\le r^2(p_x-s)^2$ and the local quotient costs at most $B(q_x)+J(q_x)o_x$, its mean cost is bounded by
$$
 B(r)+r/2+b_2r^2z+c(s+D-R)+(r/2+j_2r^2z)(D/R+v).
$$
The comparison uses the normalized quotient source $S(w,h)-S(w-D,h-v)$. This is a lower bound after dividing the dimension by $n$, by the integer-monomial pairing of the uniform proof. It is nondecreasing in $w$ for each realized $D$ by the same pairing, and concave in $D$. Split $0\le z\le V$ into twelve equal intervals. Use the left endpoint for the source and the right for the cost. Testing both endpoints of $vR\le D\le13s$ gives normalized surpluses exceeding **15,557** and **103,929**. A secondary equation coprime to $g$ results. Its resultant with $g$ has ordinate degree at most $v\lfloor w/R\rfloor+hb_0$, less than the eligible population, a contradiction. [Adaptive local quotient calculation](sixteenth-list-adaptive-quotient.md)

## The squared linear factor in a quartic denominator

For $v=1$ use the order-20000 uniform comparison. Write $g=A+BV$, $a=\deg_Y B$, $b=\lfloor D/R\rfloor$, $e=D-R$. The special case $g=V$ is excluded by the pair bound $Rn/p$ for distinct solutions in characteristic $p$ and zero common sites in characteristic zero. For each $(a,b)$ use the existing coefficient, plane intersection and occupancy bounds, including the discriminant or repeated-factor bounds for $a=4$. One interval needs a sharper estimate, namely $a=4,b=5$ when $B=C L_1^2 Q$, where $C$ is the univariate content, $L_1$ primitive linear in $Y$ and $Q$ primitive irreducible quadratic. Write $c,\ell,q$ for their normalized weights. Then $c+2\ell+q\le e$, $\ell\ge R$, $q\ge2R$. Discard also the at most two solutions where $L_1$ or $Q_Y$ vanishes identically. Combined with the previously discarded derivative and singular solutions, the loss is at most $3b_0^2$. [Ordinary comparison and cases of quartic denominators](half-list-joint-occupancy.md#a-stronger-agreement-bound-from-the-quartic-denominator)

Use $U=X-x$, $S=Y-y$ at a physical site with received ordinate $y$. Let $m$ be the minimum ordinary multiplicity of $A,B$. Call the site radial if $UA_m+SB_m=0$ for their homogeneous terms of degree $m$. At a nonradial site $o=m$, each hitting slope solves a nonzero polynomial of degree at most $o+1$, and the plane intersection length is at least $o^2$. At a radial site $U$ divides the nonzero $B_m$, and the term involving the new derivative variable at the next order gives $o=m+1$. The lower intersection charge is $(o^2-o-1)_+$. The slope-class multiplicity count at all nonradial sites gives
$$
 \mathbb E\left[(p_x-s)^2+{\bf1}_{\rm nonradial} p_x^2/(o+1)\right]
 \le R-s^2+(2s-R)/(L-3b_0^2).
$$
This is the same ordered-pair count used at orders zero and one in the previous proof, now applied at each site where the slope count is finite. [Radial initial forms and intersection charges](quarter-list-darboux-cofactors.md#exceptional-collision-classes)

Off the roots of $C$, at a radial site the factor $U$ in the initial form of $B$ must come from $Q$. A primitive linear factor has an ordinate term in its initial form whenever it vanishes. Primitivity of $Q$ makes its specialization nonzero. Since its initial form is divisible by $U$ and its ordinate degree is two, its specialization has a double root at $y$, its ordinary multiplicity is one and $Q_Y(x,y)=0$. Thus $m$ equals one or three according as $L_1(x,y)$ is nonzero or zero. The only possible radial orders there are two and four. At any site off $C$ with $o\ge3$, the coefficient derivative estimates force multiplicity at least three in the specialization of $B$ at $y$, so $L_1(x,y)=0$.

There are two cases. If the rational roots of $Q_Y$ and $L_1$ coincide, primitivity gives $Q_Y=w(X)L_1$. At a radial site off $C$, $Q_Y(x,Y)$ is nonzero because $Q(x,Y)$ has degree two and the characteristic exceeds two. Hence $L_1(x,y)=0$ there, and its radial order must be four. If the roots are distinct their resultant is a nonzero univariate polynomial of normalized degree at most $\ell+(q-R)-R\le e-c-3R$. Every simultaneous zero at a site uses at least one unit of this resultant's degree.

Set $I_L=1$ off $C$ when $o\ge3$, and also at a radial site off $C$ in the common-root case. Set $I_Q=1$ at all radial sites off $C$. These indicators certify zeros of $L_1,Q_Y$, respectively. Set $\Phi_j=\max(0,o-j-1,{\bf1}_{o>j})$. If $h$ is the lesser of $\operatorname{ord}_x C$ and $\max(1,\Phi_0)$, then $\Phi_4\le h$, $h=0$ exactly off $C$, and $\mathbb E h\le c$. The coefficient inequalities are $\mathbb E[h+p_x(\Phi_j-h)_+]\le e-jR$. Indeed the left side only decreases when the true content order is clipped. Evaluation on the retained words and degree addition give
$$
 \mathbb E[h+p_x(2I_L+I_Q)]\le e-R,\qquad
 \mathbb E[h+2p_x I_L]\le e-2R .
$$
In the distinct-root case the resultant also gives $\mathbb E[h+I_L I_Q]\le e-3R$.

For both cases the verifier enumerates the integer order, clipped content order and radial flag. For each site type its costs have degree at most two in $p_x$. Nonnegative rational dual weights give a pointwise upper bound on the order, checking the endpoints and interior maximum throughout $0\le p_x\le1$. The resulting mean upper bound is affine in $D$ and lies strictly below the concave quotient threshold on each closed test interval. The other linear factors use the same exact comparison as the previous half-rate proof. Across all **208** intervals the least normalized gap exceeds **0.00291**. Thus each positive-derivative factor accounts for fewer than $L$ words. Summing over at most three factors and the at most eighteen derivative-independent words proves the claim.

## An additional resultant gives 703/1000 agreement

At **703/1000** agreement the same hypotheses give at most **1,800,019** words, hence safety on both designated half-rate codes through **318,901,321 errors**. Use primary order fourteen and derivative cap three, giving $b_0=19$, and keep $L=600000$. The same adaptive comparisons exclude derivative degrees two and three with normalized surpluses exceeding **2,954** and **84,751**.

In the quartic case $B=C L_1^2 Q$, the numerator $A$ is coprime to the linear pole factor $L_1$. The nonzero resultant of $L_1$ and $A$ has normalized degree at most $D+b(\ell-R)$. Indeed $\deg_Y A\le b$ and evaluating $A$ on the rational root of $L_1$ and clearing its denominator gives this weighted bound. Wherever $I_L=1$, the ordinate coefficient of $L_1$ is a unit, by primitivity. Its rational root $z(X)$ is regular there and hits the received ordinate. Along this graph $g(X,z,z')=A(X,z)$ because $B(X,z)=0$. The defining radial substitution gives order at least $o$ on every regular graph through the received point. In particular the resultant has order at least $o$ at each such site. Since $\ell\le(e-c-2R)/2$, this gives the additional inequality
$$
       \mathbb E\big[(b/2)h+o I_L\big]\le D+b(e/2-2R).
$$
The comparison with this row passes on **226** linear-factor intervals, with minimum normalized gap above **0.00117**. It also verifies the earlier 88/125 claim in 204 intervals with minimum gap above 0.005. [Both normalized certificates](../../../scripts/probes/probe_half_cubic_uniform.py)
