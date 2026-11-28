# Four collinear heads locate the first-prime quarter MCA threshold to one error

Let $E$ be the first quarter-rate MCA failure at the first designated prime on the group of order $n=2^{30}$. Let $E_4$ be the first failure which a single received pair realizes using at most four collinear polynomial heads. Write $E_3$ for the corresponding first failure using three heads. Collinearity is over the coordinate function field, and each assigned scalar must satisfy the original nonjoint-support condition. Then

$$
                         E_4-1\le E\le E_4 .
$$

If $E<E_4$, then $E+1=E_3=E_4$, and the maximum three-head root score is $3$ or $4$ modulo six. In particular $E$ equals $E_4$ whenever $E_4<E_3$.

Through **472,957,708 errors**, an overrun exists exactly when one exists using at most four collinear heads. This extends the previous four-head decision interval by 97 errors. Through **479,930,027 errors**, an overrun that has no three-head realization either has a four-collinear-head realization or has all but one selected label on three collinear heads. The unrestricted first failing count still lies between 447,392,428 and 480,946,859. The proof uses the existing written quartic surface classification and the exact three-head reconstruction. [Quartic classification](quarter-collinear-interval.md) · [Three-head reconstruction](quarter-three-head-root-score.md)

## The common scalar on the core union

Write $d=n/4-1$, $t=n-e$, and take $447392428\le e\le480946858$. Select $n+1$ distinct bad labels with one actual support and polynomial per label. The classification either places all of them on four collinear heads or gives three rich collinear heads and at most 2047 remaining labels. In the latter case, represent the three heads as

$$
            (A,B)+f_i(P,Q), \qquad i=1,2,3,
$$

where $(A,B)$ is one of the heads, $P,Q$ are coprime and $s=\max(\deg P,\deg Q)\ge1$. These directions have no simultaneous zero and $\deg(f_i-f_j)\le d-s$. Let $x$ count subgroup sites with exactly one equal pair among the three heads and $r$ count sites where all three agree, independently of the received value. Write $c_i$ for the three full joint core sizes, $U$ for their union and $h=n-|U|$. Their assigned populations are $L_i\ge2048$ with $L=\sum L_i\ge n-2046$.

Set $V=3n-6(t-1)+2x+3r$. If $V>n$, the three-head root-count construction supplies an overrun at $e$ on the same subgroup. We may therefore assume $V\le n$. The three-head site count gives
$$
                L+\sum_i(L_i-2)(t-1-c_i)_+\le V .
$$
In fact $L_i>2048$ for each $i$, since the other two each have at most $e+1$ labels and $n-2046-2(e+1)>2048$. Consequently every $c_i\ge t-1$. Each covered site counts once towards the core sum, plus at most one extra on an equal-pair site and two on an all-equal site. Hence
$$
 h\le n+x+2r-3(t-1)=(V-n+r)/2\le r/2.
$$
The three polynomial differences give $x+3r\le3(d-s)$. Using $V\ge n-2046$ and $h\le r/2$ therefore yields
$$
               h+s\le d-t+1+n/3+341\le33,554,772 .
               \tag{1}
$$

An outsider with scalar $z$ and witness polynomial $q_z$ gives the rational function
$$
              g_z=\frac{q_z-A-zB}{P+zQ}.
$$
Its denominator polynomial is nonzero because the direction is nonconstant. A function equal to $f_i$ is already explained by that head. On $U$ the received value has a unique scalar coordinate along $(P,Q)$. On an outsider agreement site there, its numerator equals that coordinate times its denominator, including when both sides vanish. A primary word $f_i$ has at least $t-1$ such matches in $U$, and an outsider has at least $t-h$.

Two different outsider functions can match together at most $d+s$ times, by their nonzero cross determinant. Two different primary functions can match together at most $d-s$ times. One outsider and a different primary function have at most $d$ matches in common, since the difference is the actual folded polynomial difference of two degree-at-most-$d$ words. All these bounds count sites where a displayed outsider denominator vanishes.

## At most two additional rational functions

Suppose three distinct outsider functions occur. For the six words consisting of these and the primary triple, the sum of the fifteen pair intersections is at most $3(d-s)+9d+3(d+s)=15d$. The total of the six set sizes is at least $6t-3-3h$. At each site in $U$ of multiplicity $v$, the integer inequality $\binom v2\ge3v-6$ gives
$$
            15d\ge 3(6t-3-3h)-6(n-h),
            \qquad h\ge6t-3-2n-5d\ge67,108,870 .
$$
This contradicts (1).

Lean verifies the five- and six-support counts from the actual finite sets, as well as the corresponding numerical exclusions and the repeated-class contradiction below. The polynomial degree bounds and the reduction from arbitrary received pairs use the written argument. [Kernel-checked support packing](../../../ArkLib/Research/ProximityGap/Frontier/QuarterCollinearOutsiderPacking.lean)

For **two** distinct outsider functions the pair cap is $10d-2s$. From $\binom v2\ge2v-3$ one obtains
$$
            h\ge10t-6-3n-10d+2s.
$$
Combining this with (1) gives $33t\le33d+10n+1044-9s$. Since $s\ge1$, two different outsiders require at least **479,930,028 errors**. Even at the terminal predecessor they require $s\le3,728,380$ and $r\ge2h\ge44,739,268$.

If two different scalars give the same rational function $g$, its reduced denominator divides both $P+zQ$ and $P+z'Q$. These are coprime since $P,Q$ are. Thus $g$ is a polynomial, and solving the two scalar identities shows that $A+gP$ and $B+gQ$ both have degree at most $d$. Every occurrence of this function comes from a genuine head on the same line. In fact a repeated outsider function excludes every other outsider function. To see this, let $h_\parallel$ be the number of sites outside $U$ whose received point lies on the common line. Each such site can give at most one assigned fresh scalar to the primary triple. Its joint count is zero and its optimal three-head site charge is at least three. It therefore costs at least two units of $V-L$: summing the site charges bounds twice the total primary core plus all assigned fresh incidences, and the former core total is at least $3(t-1)$. Thus $h_\parallel\le1023$.

Take two distinct labels in a repeated class. At each uncovered site off the common line, at most one of their scalar equations can hold, since the new head lies on the line. On the remaining uncovered sites both can hold. One of their supports therefore contains at most $(h+h_\parallel)/2$ sites outside $U$. On $U$ a folded match with this word is a joint agreement with the common scalar coordinate except at the at most $s$ zeros of its scalar direction $P+zQ$. Consequently the fourth polynomial function matches the common coordinate on at least $t-s-(h+1023)/2$ sites of $U$.

If a second outsider function occurs, take its at least $t-h$ folded matches on $U$ alongside those fourth-head joint matches and the three primary joint sets. All four polynomial heads are on the same line and have row degrees at most $d$, so their six pairs overlap at most $d-s$ times each. The other four pair intersections each have at most $d$ sites. Applying $\binom v2\ge2v-3$ once more gives
$$
            10t-6-3n-10d+4s\le1023 .
$$
The left side is at least 22,369,636 throughout the bracket. Thus either at most four collinear heads cover every selected label, or three collinear heads cover all but at most two individual labels. The latter conclusion also holds when a single unused class happens to extend to a polynomial head.

When there is just one outsider function and it occurs once, exactly $n$ selected labels belong to the primary triple. Thus $V=L=n$. Its equation gives $2x+3r=6(t-1)-2n$, in particular $r$ is even. On the outsider support, each primary head's core contributes at most $d$ common sites. Outside it there are at most $e$ sites and only all-equal sites may contribute three cores. Therefore $3(t-1)\le3d+2e+r$, or $r\ge5t-2n-3d-3$. At $e=472957708$ the smallest admissible even $r$ is 51,130,564. It would give $x+3r=3(d-1)+5$, contrary to $x+3r\le3(d-s)$. Increasing $r$ or $t$ strengthens this contradiction. This proves the four-head decision equivalence. The computation at 472,957,709 allows four units of degree slack. [Integer checks](../../../scripts/probes/probe_quarter_mca_four_collinear.py)

## The remaining Hamming step

If neither three nor four collinear heads can explain an overrun at $e$, the primary triple must have at least $n-1$ labels. Hence $n-1\le V\le n$. At $e+1$, the same three polynomials have capacity $V+6\ge n+5$. The three-head reconstruction realizes this capacity. At the upper endpoint 480,946,859 the existing cubic witness already uses three heads. This proves $E_4-1\le E\le E_4$ and $E+1=E_4=E_3$ whenever $E<E_4$. [Exact capacity and reconstruction](quarter-three-head-root-score.md) · [Published upper endpoint](quarter-three-heads-32-fibers.md#attainment)

For the residue claim, let $S$ be the maximum of $2(r(P_0)+r(Q_0)+r(P_0-Q_0))-3m$ over the coprime reduced triples of degree $m\le D=d-1$ in the cited root-score theorem. Optimizing the common locator makes the maximum numerical three-head capacity at $e$ equal to $V_{\max}=3n-6(t-1)+3D+S$. If $E<E_4$, at $e=E$ one has $n-1\le V\le V_{\max}\le n$. Therefore $n-V_{\max}$ equals zero or one and is congruent to $4n-3D-S\equiv4-S$ modulo six. This gives the two stated residues. The new inequalities are written proofs. The probe checks the named production integers and exhausts the site charges governing the uncovered on-line points. [Arithmetic and local checks](../../../scripts/probes/probe_quarter_mca_four_collinear.py)

## Direction and locator at an exceptional first failure

Suppose $E<E_4$, and use the primary triple at $E$. Subtract its first scalar function and write the multipliers as $J(0,P_0,Q_0)$ with $P_0,Q_0$ coprime. Put $m=\max(\deg P_0,\deg Q_0)$ and let $b$ count the distinct reduced roots of $P_0,Q_0,P_0-Q_0$ on the grid at which $J$ also vanishes. The common triple count $r$ is the number of grid zeros of $J$. Let $A_0$ be the total number of grid roots in the three disjoint reduced sets. Then $x=A_0-b$, $r\le\deg J$, and $m+\deg J+s\le d$.

Replace the primitive direction by $(X,1)$ and take a common locator on $D-m$ distinct grid sites outside the three reduced root sets. There is room since $A_0\le3m$ and $n-3m\ge D-m$. The numerical three-head capacity increases by precisely $3(D-m-r)+2b$. It remains at most $n$ because there is no three-head overrun at $E$. Its starting value is at least $n-1$. The two nonnegative integer terms thus both vanish. Consequently
$$
        r=\deg J=D-m,\qquad s=1,\qquad b=0 .
$$
Every root of the common locator is simple and lies on the grid, and none is a reduced edge root. Since the two coprime linear forms of the direction induce a projectivity, every exceptional rational word has at most one simple pole *after treating it as a section of* $\mathcal O(d-1)$ on the projective source line. More explicitly, homogenize the actual numerator to degree $d$ and its denominator $P+zQ$ to degree one. The only possible pole of their quotient as such a section is the unique zero of that linear form. Different labels give different zero points, including a possible point at infinity. As an ordinary rational function in $X$ the quotient can also grow polynomially at infinity.
