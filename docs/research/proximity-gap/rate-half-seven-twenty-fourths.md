# First-prime rate-half ceiling at 313174699 errors

Take the first prime $p=365375409332725729550921208179070755120141565953$, $n=2^{30}$, $k=n/2$ and the order-$n$ evaluation subgroup from `_PrizeShapePrimeP30.lean`. Two received rows give **$n+1$ distinct MCA-bad scalars at $e=313174699=\lceil7n/24\rceil$ errors**. The security budget is $\lfloor p/2^{128}\rfloor=n$. Hence the operational supremum is at most $313174699/1073741824$. The previous sixteen-fiber construction gave $318767104$ errors. [Previous ceiling](rate-half-sixteen-fiber-ceiling.md)

Lean constructs the two received rows on the actual order-$2^{30}$ subgroup. The four joint agreement cores have 760567124, 760567125, 760567124 and 760567125 coordinates. Each of the $n+1$ distinct scalar labels supplies a further agreement outside its core. The theorems `FirstPrimeSepticCores.over_budget` and `threshold_le` give failure in the canonical MCA event and the resulting upper bound on the operational supremum. Whether an earlier error count already fails remains open. [Formal construction](../../../ArkLib/Research/ProximityGap/Frontier/FirstPrimeSepticCores.lean) · [Simultaneous distinct-label argument](../../../ArkLib/Research/ProximityGap/Frontier/FourHeadWitness.lean)

## The four degree-seven polynomials

Let $s=n/16$ and $\omega=g^s$ for the certified subgroup generator $g$. At index $i=0,1,2,3$ write $a=\omega^{4i}$ and use

$$f_i(Y)=(Y^6+aY^4+a^2Y^2+a^3)((a+\omega^2a^2)Y+\omega^5+\omega^3a^3).$$

The first factor times $Y^2-a$ is $Y^8-1$. At even powers of $\omega$ this makes three heads vanish. For the four points $y=\omega a'$ with $(a')^4=1$, put $R(Y)=Y-\omega Y^2$. Modulo $Y^4-\omega^4$, $(Y^2-a)R(Y)$ is $Y^3+\omega aY^2-aY-\omega^5$. Subtract the cubic $(Y^4-\omega^4)/(Y-\omega a)$ to obtain the negative of the linear factor in $f_i$. When $a'\ne a$, this cubic vanishes at $y$. Consequently the three heads there have the common value $-(y^8-1)R(y)$. The table gives every equality class at the literal production prime. Digits denote the indices of equal heads.

| Powers $j$, with $y=\omega^j$ | Classes |
| --- | --- |
| 0, 1, 8 | 123 and 0 |
| 2, 5, 10 | 023 and 1 |
| 4, 9, 12 | 013 and 2 |
| 6, 13, 14 | 012 and 3 |
| 3 | 13, 0 and 2 |
| 11 | 02, 1 and 3 |
| 15 | 03 and 12 |
| 7 | 0, 1, 2 and 3 |

Lean checks every entry by exact field arithmetic, using $\omega=357111556877444407914257742635116754287240874648$ from the certified generator. [Kernel-checked table and arithmetic](../../../ArkLib/Research/ProximityGap/Frontier/RateHalfSevenTwentyFourths.lean)

## Agreement cores and witnesses

Write $s=6t+4$, so $t=11184810$. Every fiber $D_j=\{x:x^s=\omega^j\}$ has $s$ points. Select $4t+3$ locator roots in $D_7$, $t-1$ in $D_3$, and $t$ in $D_{11}$. Let $H$ be the product of their linear factors. Set

$$W_i(X)=\big(XH(X)f_i(X^s),\ H(X)f_i(X^s)\big).$$

There are $s-2$ roots, giving degree at most $1+(s-2)+7s=8s-1$. At these roots receive $(0,0)$. On the twelve triple fibers receive the triple's value. On the unselected positions of $D_3,D_{11}$ receive the indicated pair's value. Split $D_{15}$ evenly between its two pairs. The remaining $2t+1$ positions in $D_7$ will match no head jointly.

The twelve triple fibers contribute $9s$ agreements to each head, and all heads share the $s-2$ locator roots. Each head belongs to exactly one of the single-pair fibers and receives at least $s-t$ agreements from it. Each also receives $s/2$ from $D_{15}$. The four core sizes, in order, are $760567124,760567125,760567124,760567125$. Every core has size at least $68t+44\ge k$.

At each ordinary position $x$ assign $-x$ to a differing head. Both received and head pairs have the form $(xv,v)$, so their folds agree there. The ordinary labels are distinct. At each remaining position in $D_7$ there are four distinct values $v$. Select $u_1$ outside their set and choose $u_0\ne xu_1$. The four mixed agreements occur at the distinct labels $(xv-u_0)/(u_1-v)$. For each earlier label at most four $u_0$ are excluded. The inequality $p>4(n+1)+1$ permits all assignments without repetition, while the new position agrees jointly with none of the heads.

The number of different labels is $n-(s-2)+3(2t+1)=n+1$. For each label, its selected head gives a folded polynomial agreeing on the entire joint core and on its fresh position. Any joint explanation on this witness has the same two polynomials as the selected head, because both rows agree on at least $k$ core points. The discrepancy at the fresh site excludes it. With $68t+45$ witnessed agreements the error threshold is $28t+19=313174699$.

The independent probe expands both received rows and checks each of the 257 and 1025 witnesses on the actual prime field at lengths 256 and 1024. At the production length it verifies the quotient classes, degree, core sizes, label count and error threshold. The complete production witness construction above is a written proof. [Reproducible probe](../../../scripts/probes/probe_rate_half_seven_twenty_fourths.py)

## Exact optimum for sixteen-fiber four-head constructions of this form

The same integer $313174699$ is the **least possible** within the following class on the production field. Take four distinct pairs $(B_0,B_1)+(A_0,A_1)H(X)f_i(X^s)$ with a coprime direction pair of positive maximum degree, and assume all four joint cores have at least $n-e-1$ positions. More than $n$ distinct fresh labels must be supplied by these four pairs. Both the received pair and the polynomials may vary. This conclusion concerns a single sixteen-fiber power quotient and a common polynomial direction.

Subtract $f_0$ and move each common quotient factor at a base fiber from the three differences into $H$. Thus $f_0=0$, no quotient coordinate has all four raw values equal, and $d=\max\deg f_i\le7$. There are at most $(8-d)s-2$ locator roots. Write $T,B,P,A$ for the respective counts of proper triples, double pairs, single pairs and all-distinct inputs on the 16-point quotient. The six nonzero pair differences have at most $6d$ roots in total, so $3T+2B+P\le6d$. When $B>0$, choose the opposite-pair product that vanishes twice at a selected double pair. It also vanishes at each triple, hence $T+2\le2d$.

Let $E$ sum the four core sizes, $L$ count fresh labels and $R$ count locator roots. Choose nonnegative rational prices $\lambda,\mu$. A base fiber with largest class $b$ and $m$ distinct classes contributes at most $s\max(b+\lambda,m\lambda,4-\mu)$ to $E+\lambda L-\mu R$. The three terms cover ordinary matches, positions with no match, and locator roots. The last term is for a matched root; an unmatched root has at most one fresh label and is covered by $m\lambda$. Thus subtracting $\lambda(n+1)$ and adding $\mu((8-d)s-2)$ to the sum of fiber upper bounds gives a valid bound for $E$. At the predecessor of the proposed optimum one requires $E\ge4(n-313174699)=3042268500$.

The exact rational verifier iterates all $d$ and all sixteen-site class counts. It uses prices at intersections of the lines $\lambda=0$, $\mu=0$, $(m-1)\lambda=b$, $\lambda+\mu=4-b$ and $m\lambda+\mu=4$, keeping the nonnegative ones. Each displayed price independently certifies its inequality. Split the triple count into $t_0,t_1,t_2,t_3$ according to which index differs. For any two indices their corresponding two triple classes together force roots of the difference of the other two heads, hence the two largest $t_i$ sum to at most $d$. The only survivors are

| $d$ | $(T,B,P,A)$ | Triple counts in increasing order |
| --- | --- | --- |
| 6 | $(11,0,3,2)$ | $(2,3,3,3)$ |
| 7 | $(13,0,j,3-j)$, $j=1,2,3$ | $(3,3,3,4)$ |

Take the largest triple block $T_0$ as the set where head 0 differs. Let $S_1,S_2,S_3$ be the other three disjoint blocks, with locators $P_i(Y)=\prod_{z\in S_i}(Y-z)$. Each $f_i$ for $i>0$ is divisible by $\prod_{j\ne i}P_j$ with $j=1,2,3$; write its remaining factor as $\alpha_i$. At each $y\in T_0$ the three ratios $\alpha_i(y)/P_i(y)$ must be the same nonzero weight $w(y)$. Rotating or inverting the quotient indices preserves all equality patterns and the degree bound, using $Y^d f_i(1/Y)$ for inversion. Therefore a dihedral representative of $T_0$ suffices.

For $d=6$, take $|S_1|=2$, $|S_2|=|S_3|=3$. The factor $\alpha_1$ is constant and nonzero, so scaling fixes $w=1/P_1$ on the three points of $T_0$. The other factors have degree at most one. To test a block $S_i$ multiply $w$ by its locator and interpolate on $T_0$: the quadratic coefficient must vanish. The exact census over all 21 possible distinguished-block orbits and disjoint surviving block pairs gives 49 head families. In 37 there is no single-pair fiber; in 12 there is exactly one. All have 11 triple fibers and no double pair. This eliminates the sextic row.

For $d=7$, each $S_i$ has size three and each $\alpha_i$ has degree at most one. Fix the first block $A$ and parametrize $w(y)=(u+vy)/P_A(y)$ on four points $T_0$. With $b_y=1/\prod_{y'\in T_0\setminus\{y\}}(y-y')$, put $c_j=\sum_{y\in T_0}b_y y^jP_B(y)/P_A(y)$ for $j=0,1,2$. A second block $B$ permits the same weight and an affine factor precisely when $c_0u+c_1v=c_1u+c_2v=0$. This follows by Lagrange interpolation, testing the top coefficient for the four values and for those values multiplied by $y$. Each surviving block gives a projective constraint on $(u,v)$. A third block must have the identical constraint and be disjoint from both. Among the 72 orbits for $T_0$ the computation finds 1122 intersecting pairs of constraint planes, none coincident, and no compatible disjoint triple. This eliminates all septic rows and proves optimality in this class. [Exact finite classification](../../../scripts/probes/probe_four_head_sixteen_fiber_optimum.py)

## Restrictions on arbitrary polynomial heads at the preceding error count

At 313174698 errors a witness needs 760567126 agreements. Suppose it obtains one agreement by folding at a fresh coordinate. Its two polynomial rows must then jointly agree with the received pair on at least 760567125 coordinates. On every injective domain of length $n=2^{30}$, at most **118 distinct half-rate polynomial pairs** can reach that joint agreement with any received pair.

For a family of $s$ such pairs let $d_x$ count the joint cores containing $x$. Distinct pairs intersect on at most $2^{29}-1$ coordinates. For every integer $a\ge0$ the inequality $d_x^2+a(a+1)\ge(2a+1)d_x$ yields
$$
2as\cdot760567125\ \le\ s(s-1)(2^{29}-1)+a(a+1)n.
$$
At $s=119$ and $a=84$ the left side exceeds the right side by 7378. For $s=4$, setting $a=2$ forces some two cores to intersect on at least 477218588 points. Their two polynomial differences have a common factor of at least that degree. Determinant multiplicity forces every other rich pair onto the same line over the polynomial fraction field. After removing the common factor, the two direction polynomials have degree at most **59652323**. If all 118 rich pairs occur, the stronger intersection bound gives direction degree at most **12961**.

These bounds apply without fixing a quotient or assuming a common direction in advance. Witnesses that need more than one fresh coordinate can have smaller joint cores. A bound on the total number of bad scalars at this predecessor remains open. [Kernel-checked incidence and direction bounds](../../../ArkLib/Research/ProximityGap/Frontier/RateHalfRichHeadCensus.lean)
