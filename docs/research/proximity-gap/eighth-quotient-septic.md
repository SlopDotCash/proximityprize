# The second-prime septic pencil on 64th roots

On the sixty-fourth roots in the second named prime field there is **no degree-seven rational function with three disjoint full seven-site fibers**. This makes **679,477,248 errors** the exact first failure for four-head witnesses in which three polynomial row pairs share a direction and their scalar differences factor through the sixty-fourth-root quotient after removal of a common locator. The fourth head is unrestricted and individual labels may need multiple fresh agreements. The eighth-rate threshold for arbitrary received pairs and polynomial witnesses remains open.

## The finite-field test

Let $p=730750818665451459101842416358141509841924915201$ and let $g$ be the named generator of order $2^{30}$. Set $w=g^{2^{24}}$ and $H=\langle w\rangle$. A degree-seven rational function with three disjoint full fibers in $H$ exists precisely when two disjoint seven-site supports $S,T$ have monic vanishers $P_S,P_T$ whose ratio takes one value at seven sites outside both. Any two full fibers can serve as the zero and pole fibers by a fractional-linear change of target. [Second-prime field and generator](../../../ArkLib/Research/ProximityGap/Frontier/_PrizeShapePrimeP30Second.lean)

The seven cyclic gaps between positions of a prospective third fiber sum to 64. Some two successive gaps total at most 18, since otherwise the sum of all seven adjacent pairs would be at least 133 instead of 128. Rotation and inversion preserve existence of the rational map and its fiber cardinalities. They move the three corresponding exponents to $0,a,b$ with $2\le b\le18$ and $1\le a\le\lfloor b/2\rfloor$. There are 81 such anchors. Inversion acts by $X\mapsto X^{-1}$; it does not require a Galois action on the finite field.

For each anchor define $\chi(x)$ by
\[
  g^{\chi(x)}=x^{(p-1)/2^{30}},\qquad \chi(x)\in\mathbb Z/2^{30}\mathbb Z.
\]
The verifier obtains each of its thirty bits by repeated powering and checks the resulting equality in the production field. For every seven-site support $S$ outside the anchor, compute the two components
\[
  \chi(P_S(w^a)) - \chi(P_S(1)),\qquad
  \chi(P_S(w^b)) - \chi(P_S(1)).
\]
Each component is a sum of seven precomputed differences. A pair with constant ratio at the three anchors has both signatures equal. The enumerator sorts all $\binom{61}{7}=436,270,780$ keys, regenerates the supports having a repeated key, and filters out pairs with an intersecting root set. It then checks the exact ratio at the actual field elements and measures its fiber on all 64 sites. A collision in the character can therefore add a candidate but cannot discard a solution. [Character and exact field check](../../../scripts/probes/probe_mu64_septic_character.py) · [Complete support enumeration](../../../scripts/probes/probe_mu64_septic_character.cpp)

The complete run covered **35,337,933,180 anchor/support pairs**. Among **35,139** disjoint pairs of supports matching the character signatures, **35,075** had the required exact ratio on their anchor. The largest fiber containing its anchor had size four on 76 anchors and size three on the other five. Hence no seven-site third fiber exists. The SHA-256 of the 81 ordered result rows is `c88ce93b45844b4842081799ebd765a34873994c050674be13fa759f926ee8e5`. Each row includes the digest of its sorted exact root-set pairs and their entire fibers. Reproduce the result using `python3 scripts/probes/probe_mu64_septic_character.py`. One worker uses about 3.6 GB of RAM.

The same negative result applies over every extension of the named field, since normalized vanishers and their ratios on these sites already lie in the prime field. It also rules out a complex septic pencil on the sixty-fourth roots. A characteristic-zero identity among the cross-multiplied vanisher values in $\mathbb Z[\zeta_{64}]$ would specialize at $\zeta_{64}\mapsto w$ to the named field, where all sixty-four sites are still distinct.

## The restricted MCA threshold

Consider the scalar four-head descriptions on the length-$n=2^{30}$ named power domain at dimension $k=n/8$. Three distinct row pairs have the form
\[
  W_i=W_*+J(X)(U(X),V(X))F_i(X^s),\qquad s=n/64,
\]
where $U,V$ are coprime, at least one is nonzero, and all row degrees are below $k$. The fourth row pair $W_3$ and the received pair can be arbitrary. First suppose $W_3$ is transverse, meaning $\det(W_3-W_*,(U,V))$ is a nonzero polynomial. A counted scalar has a bad folded witness represented by one of these heads. Its support may require multiple coordinates outside that head’s full joint core.

Subtract $F_0$ and absorb it into $W_*$. The resulting base is $W_0$, with degree below $k$, and the transverse determinant is unchanged. Remove all common quotient zeros by dividing both remaining differences by their vanisher and multiplying $J$ by its substitution at $X^s$. Let $d$ be the largest remaining difference degree, $G$ the number of domain roots of $J$, and $\ell=\max(\deg U,\deg V)$. A difference attaining $d$ in a coordinate attaining $\ell$ gives $G+\ell+sd\le k-1$, so $d\le7$. For each of the three pairs let $r_{ij}$ count its quotient coincidences. They are disjoint and each $r_{ij}\le d$. Thus
\[
 \sum_{i<j}r_{ij}-2d\le 6.
\]
For $d\le6$ this follows immediately. At $d=7$ its only exception would be three disjoint seven-site fibers, exactly the case tested above. The cubic over the thirty-second-root quotient attains six after substituting $X^2$ on the sixty-fourth-root quotient. Had a full septic existed, the earlier $k-2$-overlap allocation would have given 2,260,729,864 labels at 675,282,945 errors, an improvement of 4,194,304 over its cubic value. The census rules out that substitution.

Let $c_i$ denote the size of the full joint core of head $i$. Count one baseline per domain site, with at most two additional triple agreements on each common root and one per pair-only coincidence away from the common roots. Where the fourth head and a triple head both match, the transverse determinant must vanish; it has degree at most $k-1+\ell$. Consequently
\[
  \sum_{i=0}^3 c_i\le n+2G+s\sum_{i<j}r_{ij} + k-1+\ell
  \le n+3k-3-\ell+6s.
\]
One core therefore has at most 394,264,575 sites. At $e\le679,477,247$ one fresh witness needs a core of at least 394,264,576. Each of the other three heads supplies at most $e+1$ labels because a mismatching site gives at most one scalar for its head. The three together supply at most 2,038,431,744, below the budget of 2,147,483,648. Lean checks the per-site multiplicity inequality, the integer core cap conditional on the census, and the three-head budget. [Lean counting lemmas](../../../ArkLib/Research/ProximityGap/Frontier/EighthQuotientCoreCap.lean)

## Witnesses that need several fresh agreements

It suffices to rule out the predecessor $e=679,477,247$ by monotonicity: a witness at an earlier count still witnesses the same scalar at this count. Write $t=n-e=394,264,577$. Assume more than $2n$ different labels can be represented. Assign each label to one representing head. If a head has $c$ joint sites and represents $L$ assigned labels, then $L\max(1,t-c)\le n-c$. Indeed, each assigned bad label requires a fresh mismatch and at least $t-c$ fresh matches, and the mismatching sites for different labels are disjoint on this head. Thus every head supplies at most $e+1$ labels. Every head also supplies at least $2n+1-3(e+1)=109,051,905$. When $c<t$, the fresh-site inequality gives $(L-1)(t-c)\le e$. Therefore **every core contains at least $t-6=394,264,571$ sites**.

Call a core rich if $c\ge t-1$. A nonrich head supports at most $1+\lfloor e/2\rfloor$ labels. Two nonrich heads would give at most $2(e+1)+2(1+\lfloor e/2\rfloor)<2n$. Thus at least three cores are rich. The core-sum bound above gives $\sum c_i\le1,577,058,301$, so the fourth core has $c\le394,264,573=t-4$. Its label count is at most $1+\lfloor e/4\rfloor=169,869,312$.

Among the three rich heads choose two from the collinear triple. Call them $i,j$ and call the remaining triple head $h$. At most $k-1$ sites in the core of $h$ can also belong to the core of $i$, by the degree bound on a nonzero coordinate difference; the same estimate holds for $j$. Thus at least $394,264,571-2(k-1)=125,829,117$ sites in the core of $h$ belong to neither $i$ nor $j$. At each such site, the received value is $W_h$. Both foreign pair differences from $W_h$ lie in the same direction. They can supply at most one distinct label, including when the second direction entry vanishes and neither supplies one.

Choose a single fresh coordinate for every label of each rich head. This selection is injective within each head. At each of the 125,829,117 sites, at least one of the two available coordinate slots of heads $i,j$ must go unused because different heads have been assigned disjoint label sets. The three rich heads together consequently supply at most $3(e+1)-125,829,117$ labels. Adding the fourth gives at most **2,082,471,939**, below $2n$ and contradicting the assumption. The Lean lemmas check the unused-slot count and the integer implications for the deficient head. [Predecessor and counting certificates](../../../ArkLib/Research/ProximityGap/Frontier/EighthQuotientCoreCap.lean)

Finally, suppose the fourth head lies on the same line over the function field. If two heads are identical, three distinct heads account for at most $3(e+1)$. Otherwise all triple determinants vanish identically and all evaluated row pairs are collinear at every site. Under the same supposition of more than $2n$ labels, the unconditional lower bound $c_i\ge394,264,571$ still applies. Three distinct cores cover at least $3(394,264,571)-3(k-1)=780,140,532$ sites by the pairwise polynomial root bound. At these sites every possible foreign label comes from the same pointwise direction, giving at most one distinct scalar per site. At each remaining site four heads can give at most four. The total is at most $4n-3(780,140,532)=1,954,545,700$, again below $2n$.

The transverse cubic construction gives 2,148,807,811 actual one-fresh labels at the next count. It uses $\ell=1$, $U=X$, $V=1$, and cubic values on $X^{2s}$. Thus the first failure for this class is **679,477,248**, even allowing multiple fresh agreements per label. The unrestricted first failure and the effect of more general quotient supports remain open. [Attaining construction](eighth-transverse-mobius.md)

## Necessary benefit for a construction on the full domain

The private-site argument also applies before choosing a quotient. At $e=679,477,247$, three cores are rich and every core has size at least $t-6$ in any hypothetical failure with a collinear triple and arbitrary fourth. If the remaining core had size at most $t-3$, its label count would be at most $1+\lfloor e/3\rfloor=226,492,416$. Combining this with the two rich heads’ $125,829,117$ unused slots gives at most $2,139,095,043$ labels. Thus every core must have size at least $t-2$, and the sum of the four core sizes is at least $4t-5$.

Write $d$ for the maximum actual difference degree of the three scalar polynomials after their common domain roots are removed. Write $r_{ij}$ for their remaining pair-only root counts. The same degree and coverage argument on the original domain gives $\sum c_i\le n+3k-3-\ell+\sum r_{ij}-2d$ for a transverse fourth head. Any improvement with a collinear triple must consequently satisfy
\[
  \sum r_{ij}-2d\ \ge\ 100,663,298+\ell .
\]
The existing cubic has benefit 100,663,296. This necessary condition holds without a power-quotient hypothesis. In particular, on the next quotient of size 128 a degree-13 pencil needs three full 13-site fibers, degree 14 permits at most one lost site across its three fibers, and degree 15 permits at most two.

## The sign-symmetric noncollinear quartet

A different construction asks for a full septic $A$, its opposite $A(-X)$, two even split sextics $C,D$, and the singleton pair $\{1,-1\}$. It needs $A=u(X-1)C-v(X+1)D$ with nonzero scalars. Each of the seven roots of $A$ chooses a distinct antipodal class outside $\{1,-1\}$, giving $\binom{31}{7}2^7=336,585,600$ possibilities. For a remaining antipodal pair $\{t,-t\}$, a root of $C$ requires $A(t)/A(-t)=(-t-1)/(t-1)$, and a root of $D$ requires $(-t+1)/(t+1)$. These are the same necessary equations used in the earlier thirty-two-site test. [Quartet identity](second-prime-four-noncollinear-cubics.md#the-antipodal-degree-seven-extension)

For fixed $t$, selecting the sign of a root $x$ contributes $(t-x)/(-t-x)$ or its reciprocal. Partition the thirty available classes into two sets of fifteen. For each possible number chosen from the first set, tabulate products on the smaller side and test complementary products on the other. This takes place directly in the named prime field. Exactly 174,528 supports have one eligible pair and 96 have two. None has three eligible pairs in total, whereas splitting both sextics requires six, three of each type. This excludes this specific noncollinear construction on $\mu_{64}$ as well. [Exact production-field enumeration](../../../scripts/probes/probe_mu64_antipodal_quartet.py)
