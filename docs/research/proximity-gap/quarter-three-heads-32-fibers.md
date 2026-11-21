# The first named quarter-rate ceiling is sharp among three heads on 32 fibers

At $n=2^{30}$ and dimension $k=n/4$, the first named prime allows exactly $n$ bad scalar labels. The known attack at **480946859 errors** is optimal among the three-head descriptions below. The bound allows arbitrary received rows and multiple fresh agreements for the same label. The unrestricted predecessor at 480946858 errors is open. [Existing unconditional Lean ceiling](../../../ArkLib/Research/ProximityGap/Frontier/_P1RateQuarterAdjacentExactPin.lean)

## The head family and its scalar labels

Write $s=n/32$, use the smooth subgroup as domain, and fix three distinct polynomial row pairs of degree below $k$ of the form
$$W_i=(A,B)+(U,V)f_i(X^s).$$
Here $A,B,U,V$ are polynomials, and $(U,V)$ has nonconstant projective direction over $F(X)$. Dividing their common factor leaves a pair with maximum degree at least one. Let $R$ count the domain zeros common to $U,V$. Subtract $f_0$ from all three quotient polynomials, absorbing it into $(A,B)$. With $d=\max_i\deg(f_i-f_0)$, the degree of a nonzero row difference yields $R+sd\le8s-2$, so $d\le7$.

A label $\gamma$ is represented if, for some head $i$, the folded polynomial $W_{i,0}+\gamma W_{i,1}$ agrees on at least $t=n-e$ sites of a nonjoint witness set. Such a set contains a site where the two rows fail to equal $W_i$. Given $L>n$ distinct represented labels, assign one head to each valid label. Let $L_i$ be its population, $C_i$ the full joint agreement set, and $c_i=|C_i|$. A fresh agreement occurs outside $C_i$. Write $J$ for the total number of fresh incidences of the assigned labels across all sites. Then
$$J\ \ge\ \sum_i L_i\max(1,t-c_i).$$
For one head, distinct labels use disjoint fresh sites, so $L_i\max(1,t-c_i)\le n-c_i$ and $L_i\le e+1$. If $e\le480946859$, then $L_i\ge n+1-2(e+1)>2$ for each $i$.

## Counting incidences across the 32 quotient fibers

At a site where the three evaluated heads give $b$ different vectors, an unmatching received pair creates at most $b$ fresh incidences. If the received pair matches a head, the other head vectors lie on the same line through it, giving at most one fresh scalar label. An incidence is counted for that label's single assigned head. Consequently the local contribution to $2\sum_i c_i+J$ is at most 3 for three distinct head values, 5 for a single pair coincidence, and 6 for a triple coincidence. A common zero of the direction can raise any of these three bounds by at most 3.

Let $Q$ be the $q$ quotient sites where all three scalar values coincide. Each $f_i-f_0$ is divisible by $L_Q$, the monic vanisher of those sites. Put $d'=d-q$ and let $r_{ij}$ count the quotient sites outside $Q$ where heads $i,j$ coincide. Each $r_{ij}\le d'$. Summing the site bounds gives
$$2\sum_i c_i+J\le3n+2s\sum_{i<j}r_{ij}+3sq+3R.$$

For $d'\le6$, the quantity $2\sum r_{ij}+3(8-d')$ is at most $24+3d'\le42$. For $d'=7$ we have $q=0$. Two pairs with seven roots and a third with at least six would give disjoint seven-sets with constant vanisher ratio on the six roots of the third difference. The strengthened septic census rules this out in every characteristic above $2^{118}$. Thus $\sum r_{ij}\le19$ and the same quantity is at most 41. In all cases,
$$2\sum_i c_i+J\le 3n+42s-6.$$
The septic calculation examines 454 orbits of five test points and requires a sixth match in each tested specialization. It finds no candidates. [Norm lift and finite census](mu32-quarter-list-threshold.md#three-finite-fiber-facts) · [Exhaustive verifier](../../../scripts/probes/probe_mu32_quarter_fibers.cpp)

Set $u_i=\max(0,t-1-c_i)$. Since $J\ge L+\sum_iL_i u_i$ and $c_i\ge t-1-u_i$, the same left hand side is at least $6(t-1)+L+\sum_i(L_i-2)u_i$. Therefore $6(t-1)+n+1\le3n+42s-6$, giving
$$t\le1+\left\lfloor(53s-4)/3\right\rfloor=592794965.$$
Every such attack needs at least **480946859 errors**. Any strict loss of one unit in $2\sum r_{ij}+3(8-d')$ would lose $s$ in the site bound. At the extremal count the slack is only one, so $d'=6$ and all three reduced edge differences have six roots outside $Q$. The degree-six census forces antipodal root sets. Thus even if seven-degree quotients are permitted, removing their shared zeros leaves three cubic fibers pulled back from the sixteenth roots.

## Attainment

On $\mu_{16}=\langle w\rangle$ choose the disjoint three-sets $A=(0,1,8)$, $B=(2,9,10)$ and $C=(3,5,7)$. Set $g_0=0$, $g_1=L_A$ and $g_2=L_B L_A(w^3)/L_B(w^3)$. An identity in $\mathbb Z[w]/(w^8+1)$ gives $g_1=g_2$ on $C$. Each of the three pair differences has exactly three roots, and there is no triple coincidence. [Integral witness and arithmetic](../../../scripts/probes/probe_quarter_three_heads_32.py)

Use $f_i(Y)=g_i(Y^2)$, so the three pair-only types occupy $6s$ sites each. Of the $14s$ all-distinct sites choose $2s-2$ as zeros of a locator $H$ and another $s$ as holes. Take $W_i=(XH,H)f_i(X^s)$. Choose the received value equal to the coincident pair on each pair-only site, zero on the locator zeros, and distribute the $11s+2$ ordinary singleton sites evenly among the three heads. Each head has $12s+(2s-2)+(11s+2)/3=592794964$ joint sites.

On every ordinary nonlocator site choose the label $-x$ for an unmatched head. At each hole choose an off-line received pair supplying three new labels. Explicitly, choose a second entry different from all three head second entries. For each head and each previous label there is only one forbidden first entry. One more first entry would put the received pair on the common line. The named field has more than $3(n+2)+1$ elements, so the construction can continue. The $n+2$ labels each gain a fresh site. Since the joint core has at least $k$ sites, any joint explanation would agree identically with its head, contrary to the fresh mismatch. The three row degrees meet the stated cap.

## A sharp degree gap on complex dyadic roots

For every dyadic $N\ge16$, three disjoint full fibers of a rational map on the complex $N$th roots have **no common degree strictly between $3N/16$ and $N/4$, or above $N/4$**. Here a full fiber consists of all $m$ distinct roots of one degree-$m$ member of a pencil spanned by two coprime degree-$m$ vanishers. Both $3N/16$ and $N/4$ are attainable by the preceding cubic after composition with $X^{N/16}$, and by the power map $X^{N/4}$.

For the descent, if any of the three fibers has at least three points in each exponent parity, the dyadic parity lemma makes the other two antipodally closed. Their vanishers are even, so the third member of the pencil is even too. Otherwise, for $m\ge5$, each fiber has one dominant parity class and at most two points in the other. Two fibers share a dominant class $E$. Applying the parity lemma in their two roles makes all three fibers antipodal on the opposite class. If the third fiber is dominant there, the first two are antipodal on $E$ as well, so all three are antipodal everywhere. If all three are dominant on $E$, disjointness gives $3(m-2)\le N/2$. [Parity lemma and its hypotheses](production-ratio-lifting.md#the-parity-constraint-in-the-complex-field)

For $N\ge64$ and $m>3N/16$ the last inequality fails. Thus all fibers are antipodal, and passing to $X^2$ divides the degree and domain size by two. At $N=32$, degree seven is excluded by the preceding finite census. Degrees eight through ten satisfy $3(m-2)>16$ and descend to $N=16$. At $N=16$ the only degree above three other than four is five by disjointness. It is excluded by the five-set census on the containing $\mu_{32}$. This proves the claim by descent. In particular the first named domain order has a characteristic-zero gap of **67,108,863 consecutive degrees** between $3N/16$ and $N/4$. The positive-characteristic three-head bound above uses the 32 quotient sites, where the norm lift is valid. Uniform transfer of the full degree gap to the $2^{30}$-element subgroup of a named prime remains open.
