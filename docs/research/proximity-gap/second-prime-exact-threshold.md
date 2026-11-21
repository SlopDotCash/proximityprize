# The second rate-sixteenth threshold and a field-size interval

Let $n=2^{30}$, $k=2^{26}$, and $d=k-1$. For the repository's second prime
$p=730750818665451459101842416358141509841924915201$, Lean proves that
**715827881** is the last safe integer error count and **715827882** is the
first failure. At tolerance $2^{-128}$ the safe real radii on its smooth
evaluation domain are exactly $0\le\delta<715827882/n$. The operational
supremum is $715827882/n$. [Exact Lean theorem](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeCubicExact.lean) · [Endpoint failure](../../../ArkLib/Research/ProximityGap/Frontier/_ThreeCoreSecondPrimeBracket.lean)

In fact, let $B=\lfloor p/2^{128}\rfloor$ for any prime $p$ with
$2013265923\le B\le2147483648$. On **every injective** length-$n$
evaluation domain over this field the first bad count is $\lfloor B/3\rfloor$.
All positive interleaving widths have the same MCA error. This covers
134,217,726 consecutive integer budgets. Lean also proves the exact worst-pair probability $3(e+1)/p$ for every $671088641\le e\le715827881$ whenever $B\ge2013265923$. [All-domain budget and probability theorem](../../../ArkLib/Research/ProximityGap/Frontier/UniversalCubicBudgetWindow.lean) · [Interleaving theorem](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)

A second Lean proof uses one coordinate change for the selected cubic sections and both received rows. At most 161 labels are lost. The retained sections force a large common divisor of two ordinary polar resultants. Their local intersection budgets bound the sum of the received multiplicities, so a low-weight cubic has fewer than 1,342,177,249 labels. The proof recovers the named cutoff independently and extends the budget interval to every injective length-$2^{30}$ domain over every finite field of characteristic greater than $1,320,000,000$. [Independent named proof](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeTerminalCharge.lean) · [Full budget interval](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeOrdinaryWindow.lean)

## An upper bound for every received pair

Write $b(e)$ for the maximum number of bad scalars among all two-row received
words at $e$ errors. We prove $b(e)\le3(e+1)$ for
$671088640\le e\le715827881$. Put $t=n-e$ and $t_0=357913943$.
Choose $3(e+1)+1$ distinct bad scalars and a degree-at-most-$d$ polynomial
$q_z$ for each, with its witnessing set of at least $t$ sites. The folded
rows agree there with $q_z$, and no two codewords explain the two original
rows throughout that set. We use that last property when counting affine heads.

The interpolant at $t_0$ has value degree at most four and total degree
in $(Z,Y)$ at most 34. It contains all the chosen points $(z,q_z(X))$
over $K=\overline{\mathbb F}_p(X)$, since $t\ge t_0$. Factor it over
$K[Z,Y]$ and take primitive representatives. Factors independent of $Y$
account for at most 34 labels altogether. We use the following thresholds
from the proofs of the two largest factor degrees.

* A quartic would carry at least $3(e+1)+1-34\ge2013265890$ labels.
  In the quartic argument the population enters first through the inequality
  $34\cdot119<M$. The remaining population test is
  $M-144903915>268435546$. Both hold even at this smaller $M$.
  The weighted spaces and all local dimension and exception counts use $t_0$.
  The branch in which the reverse second derivative vanishes has at most four
  points. [Quartic elimination](second-prime-quartic-intrinsic.md)
* A cubic allows at most one other positive-value-degree factor. A nonlinear
  value-linear factor carries at most 184 points. An affine head carries at
  most $e+1$ by the fresh-agreement count below. Hence the cubic carries at
  least $M=2(e+1)+1-34\ge1342177249$. Its weight is at most 290805098
  because $34\cdot2^{25}<M$. The small-polar case constructs an auxiliary
  equation of value degree at most two and scalar resultant degree at most
  1200000068, vanishing on at least $M-164$ labels. The large-polar case
  constructs one vanishing on all $M$, with resultant degree at most
  1200000062. Both contradict coprimality. The local estimates, interpolation
  spaces and exact dimension surpluses use the same $t_0$ throughout.
  [Cubic elimination and polynomial matrix](second-prime-terminal-cubic.md) · [Local intersection proof](second-prime-persistent-singularities.md)
* The remaining nonlinear factors of positive value degree carry at most
  4128 labels apiece. These estimates use the weight strictly below $t_0$
  of the initial interpolant and the fact that every chosen point has at
  least $t_0$ agreements. [Linear and quadratic estimates](PROGRESS.md#low-degree-factors-of-the-quartic-cannot-carry-a-second-prime-violation)

It remains to count affine factors. Call a line carrying more than 512
chosen points large. Two such points determine a head $(A_i,B_i)$ over
the original field, of polynomial degrees at most $d$, so that its points
have $q_z=A_i+zB_i$. Let $C_i$ be the set of sites where the received
rows equal $(A_i,B_i)$. Outside $C_i$ at most one scalar can match this
head at each site, and each witness on the head requires at least one
such match. For a line with $L$ points, $c=|C_i|$, this gives
$L\max(1,t-c)\le n-c$, hence $L\le e+1$. If $L>512$ then
$c\ge t-\lfloor e/512\rfloor\ge z_0=356515842$.
Distinct heads have cores meeting in at most $d$ sites.

With at most two large heads the total is at most $2(e+1)+4\cdot4128+34$,
less than the selected population. Suppose three large heads are
noncollinear as points $(A_i,B_i)$ over $K$. Their nonzero affine
determinant has coordinate degree at most $2d$. If a site belongs to
$v\ge2$ of these cores, subtracting one coincident row from the other
$v-1$ rows shows divisibility by $(X-x)^{v-1}$. Their core union therefore
has at least $3z_0-2d$ sites. A selected point outside all three lines can
agree at at most $d$ sites of each core by the polynomial root bound.
It has at most $n-3z_0+5d=339738613<t_0$ agreements. Thus the three
heads contain every selected point, more than their combined capacity.

In the remaining case all $j$ large heads are collinear over $K$, where
$j=3$ or 4. All their affine determinants still vanish at each site.
On the core union $U$, a site agrees with one received head pair. Every
distinct evaluated head pair lies on the same line through this pair.
Thus at most one scalar gives a fresh agreement across the large heads
there. Off $U$ there are at most $j$ fresh scalars per site. Since
$|U|\ge jz_0-\binom j2d$, these heads carry at most
$j n-(j-1)(jz_0-\binom j2 d)$ distinct labels. For $j=3,4$ these
bounds are 1484783598 and 1224736726. Even allowing $4\cdot4128+34$
other labels, both fall below $3(e+1)+1$. This completes the upper bound.


Lean now checks this final count directly for any selected subset of the literal MCA-bad scalars. Given at most four determined secants with more than 512 labels apiece covering all but 16546 selected labels, their joint-core packing and determinant geometry imply the bound $3(e+1)$ throughout the displayed interval. In the collinear case the formal proof maps every fresh agreement either to the unique scalar at a covered coordinate or to its coordinate and source head outside the union. At the named prime, proving this geometric coverage for each hypothetical sample of $2147483649$ bad labels gives the exact operational threshold by combining the safe predecessor with the existing three-core attack. The following reduction now derives this coverage from three explicit nonlinear population bounds. [Conditional named endpoint and unconditional head count](../../../ArkLib/Research/ProximityGap/Frontier/TerminalCollinearHeadCount.lean)


The value-linear factor step also has a direct Lean proof on the selected polynomial sections. For an irreducible factor $A(X,Z)Y+B(X,Z)$ of total $(Z,Y)$-degree at most 34, any 185 rich labels force 35 of their selected points onto one base-field secant. Restricting the factor to that secant produces a polynomial in $Z$ of degree at most 34 with 35 distinct roots. It vanishes identically, and primitivity forces every label carried by the factor onto the same secant. The theorem allows an arbitrary extension field for the coefficients and derives the factor degree bound from the actual interpolation support. [Kernel-checked value-linear exclusion](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeLinearFactor.lean)

### The three remaining nonlinear population bounds

The value-linear factor argument now runs directly on the actual interpolation divisor. Write the irreducible factor as $A(X,Z)Y+B(X,Z)$. Restricting a degree-34 interpolant to two generic lines $Y=cZ$ gives $\deg_Z B\le34$ and $\deg_Z A\le33$. At a coordinate where the component contains the entire received line, $A$ specializes to a nonzero polynomial. Otherwise both $A$ and $B$ would vanish there and the coordinate linear factor would divide the whole irreducible component. Thus at most 33 selected sections miss each such coordinate. At each other coordinate, at most 34 sections agree.

Among 185 selected sections the proof finds 35 for which every triple shares more than $d$ sites. The secant through any two contains all 35. Substituting its equation into the factor produces a degree-at-most-34 polynomial in $Z$ with 35 distinct roots. The secant equation therefore divides the factor. Irreducibility puts every selected section of that factor on the secant over the original finite field. [Value-linear exclusion](../../../ArkLib/Research/ProximityGap/Frontier/TerminalLinearComponent.lean)

For a selected sample $G$, a cubic factor leaves value degree at most one for every other factor together. That complementary factor accounts for at most $e+1$ labels. A quartic leaves no complementary factor of positive value degree. Vertical factors remove at most 34 labels. After the cubic and quartic alternatives are excluded, the factorization supplies at most four affine secants, with at most $34+4\cdot4128=16546$ exceptions if each remaining quadratic has at most 4128 sections. The existing head count then applies.

At the named predecessor, a sample of 2147483649 bad scalars would require an irreducible cubic with **1431655733** sections or an irreducible quartic with **2147483615** sections. The factor-count argument originally allowed a quadratic with 4129 sections. Its unconditional population cap is now **263**. For a moving squarefree part, even a degree-dropping square fiber of a degree-$r$ polynomial contributes at least $r-\lfloor r/2\rfloor$ to the order of the padded derivative resultant. A nonempty set of square fibers has cardinality strictly below four times the parameter degree. The discriminant has parameter degree at most 66. For a parameter-only square class, the secant bound is 184. The later quartic bound below reduces the Lean endpoint proof to the proper cubic. [Factor-count reduction](../../../ArkLib/Research/ProximityGap/Frontier/TerminalFactorCoverage.lean) · [Quadratic cap and remaining alternatives](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeQuadraticFactor.lean) · [Padded resultant proof](../../../ArkLib/Research/ProximityGap/Frontier/PaddedPowerSpecialization.lean)

## A matching construction on arbitrary domains

Take $671088641\le e\le715827882$, set $t=n-e$, and put
$h=\max(0,\lceil(3(t-1)-n)/2\rceil)$. Then $h\le k-2$, $t-1\ge k$,
and $3(t-1)-2h\le n$. Choose $h$ common sites and three disjoint
sets of $t-1-h$ private sites. Write $V(X)$ for the common-site vanisher.
Use the following three pairs of polynomials, multiplying both entries of
each by $V$:
\[
 (0,0),\qquad (X,1),\qquad (2X+c,3).
\]
They have degrees below $k$. At common sites assign zero rows, and on
each private set assign its owner's pair. The scalar giving agreement of
two different heads at a private site $x$ is one of
\[
 -x,\qquad -(2x+c)/3,\qquad -(x+c)/2 .
\]
Within each of the three types the labels at distinct sites are distinct.
The coefficients of $c$ in the three types are pairwise different, so
each cross-type collision at prescribed sites excludes at most one $c$.
There are at most $3n^2$ exclusions. Choose $c$ outside them.
Each private site supplies two fresh labels, one for each nonowner.
For a fixed unordered pair of heads, a private site of either owner
is used just once for that type.

At each remaining free site divide the row to be chosen by $V(x)\ne0$.
Fix its second entry to be 2 and choose its first entry $a$. The fresh
labels against heads $i$ are $(A_i(x)-a)/(2-B_i(x))$ for the three
unscaled pairs above. They are affine functions of $a$ with nonzero,
distinct slopes. At most $3(3n)+3$ choices cause a collision with any
earlier label or between the three new labels. The fields under
consideration have $p>\max(3n^2,9n+3)$. Choosing the free rows successively
therefore supplies three more fresh labels per free site.

For each head, its common and private sites form a core of size $t-1$.
At every site outside the core there is a fresh scalar for this head.
The core together with that site witnesses badness. Indeed the core has
at least $k$ sites and forces any joint explanation to equal the two
head polynomials identically, whereas its second row differs at the
extra site. All the labels have been chosen distinctly. Their number is
$3(n-(t-1))=3(e+1)$. This proves the lower bound, including for
the last displayed $e$, where only the lower bound is needed.

For $j=\lfloor B/3\rfloor$ the preceding intervals include $j-1$ on
the good side and $j$ on the bad side. Thus $b(j-1)\le3j\le B$ and
$b(j)\ge3j+3>B$. The bad event is monotone and constant between
consecutive Hamming steps. Consequently the good real radii are exactly
$0\le\delta<j/n$. [MCA and its radius predicate](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean)

The same two cubic cases extend to all multiples of 16 above this length in characteristic greater than $3n^2$. At rate $1/16$ a quadratic three-head construction also determines the adjacent plateau at $5/8$. [Uniform interval](uniform-three-head-threshold.md) · [Plateau](rate-sixteenth-three-head-plateau.md)

A second proof uses unrestricted value-degree interpolation, the raw Hessian, and two ordinary first polars. [Ordinary-polar proof](second-prime-unrestricted-jets.md)

For the quadratic discriminant, Lean proves that a squarefree bivariate polynomial of positive coordinate degree has a nonzero resultant with its coordinate derivative whenever all integers from one through its degree remain nonzero in the field. The proof uses Gauss's lemma over the rational function field in the parameter. Coefficient factors become units there, and positive-degree factors retain separability. [Squarefree coordinate resultant](../../../ArkLib/Research/ProximityGap/Frontier/SquarefreeCoordinateResultant.lean)

At the named predecessor, Lean now proves that any budget violation would force an irreducible cubic carrying at least 1,431,655,733 selected scalars. The component has coordinate/value weight at most 290,805,098 and intersects its scalar Hessian properly. The independent quadratic arguments give bounds of 2,047 and 330 selected labels. [Sharper quadratic bound](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeQuadraticFactor.lean) A quartic that divides its Hessian carries at most one, and every other quartic carries at most 268,435,546. These bounds apply to the original received rows and their decoded sections. [Remaining proper cubic](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeProperCubic.lean) · [Quadratic bound](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeQuadraticPopulation.lean) · [Quartic bound](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeActualQuarticCap.lean) · [Hessian-divisible bound](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeReverseChart.lean)

For the actual cubic, at least **1,431,655,603** selected labels are simple in the value variable. Its nonzero cubic discriminant has scalar degree at most $4m-6=130$ for scalar/value total degree $m=34$. A repeated finite section annihilates this discriminant even when specialization lowers the value degree. Thus at most 130 of the 1,431,655,733 selected labels can be multiple. The shared coordinate change preserves all received agreements and sends every simple section's value derivative to its full homogeneous degree $W-d$. The remaining cubic has $W<220000000$ and an excessive sum of multiplicities at the original received lines. For a pair of bounded polar resultants divisible by the squared section residuals at those labels, the generic gcd degree $g$ then satisfies $2(W-d)\le g+111$. The unconditional population cap is now **1,200,005,270** for the whole cubic, including multiple labels. This excludes the component and closes the safe predecessor. [Uniform population cap](../../../ArkLib/Research/ProximityGap/Frontier/UnconditionalCubicPopulation.lean) · [Discriminant degree and multiple sections](../../../ArkLib/Research/ProximityGap/Frontier/CubicSectionDiscriminant.lean) · [Common chart on all simple labels](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeMobiusSections.lean) · [Actual labels, polar defect and threshold implication](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeCubicWitness.lean)
