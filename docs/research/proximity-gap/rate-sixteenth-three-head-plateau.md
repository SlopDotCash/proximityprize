# A plateau at five eighths from three pairwise intersections

Let $n=16k\ge2^{30}$ and let the characteristic of the finite field exceed
$3n^2$. For every injective $n$-site domain the first failure of the MCA
test is at **$10k$ errors** throughout the integer budget interval
\[
 20k+1+\lfloor(10k-1)/3\rfloor\ \le B\le 30k+2 .
\]
At $n=2^{30}$ this is the interval from **1565873494** through
**2013265922**. The operational supremum is $5/8$, and the good radii
satisfy $0\le\delta<5/8$. This interval adjoins the one determined by
$\lfloor B/3\rfloor$. [Adjacent interval](uniform-three-head-threshold.md)

At the production length, Lean proves this plateau on every injective domain over every prime field in the displayed budget range, at each positive interleaving width. For finite extensions, the field cardinality gives the budget and characteristic above 1,744,830,589 suffices. The last safe count is 671,088,639 and the first failure is 671,088,640. The proof selects three distinct large polynomial heads with at most thirteen exceptional scalars, then counts fresh agreements separately on collinear and noncollinear triples. The lower construction takes three heads with one exceptional site per head and just fits the domain. [Three-head extraction](../../../ArkLib/Research/ProximityGap/Frontier/FiveEighthThreeHeadCover.lean) · [Fresh-agreement count](../../../ArkLib/Research/ProximityGap/Frontier/PlateauThreeHeadPredecessor.lean) · [Complete threshold](../../../ArkLib/Research/ProximityGap/Frontier/FiveEighthsPlateauThreshold.lean)

## The last good error count

Take $e=10k-1$, $t=6k+1$, $d=k-1$, and denote the lower endpoint above
by $B_0$. Suppose there are $B_0+1$ distinct bad scalars for one row pair.
Choose an actual witnessing set and a degree-at-most-$d$ polynomial at each.
The first-order interpolant of total scalar-value degree at most 13 and
value degree at most three exists. The number of coefficients minus the
number of site-line conditions is $50t-70d-14n$ when using the four
value slots $0,1,2,3$ with total degree at most 13. More explicitly the
sum is $14t+13(t-d)+12(t-2d)+11(t-3d)-14n=6k+120>0$.
Each chosen polynomial is a root after specializing its scalar.

A cubic factor carries at least $B_0+1-13$ labels. This exceeds the
$5n/4-34$ required by the [uniform cubic exclusion](uniform-three-head-threshold.md#weight-and-multiplicity-estimates).
The agreements exceed its $t_0$ and the starting weight here is capped at
$t-1$. For the cubic weight test use the uniform proof's independent
degree-$2^{25}$ interpolation space at $t_0$. All its members are divisible
by this cubic by Bézout. The subsequent Jacobian and jet calculations use
only the resulting weight, the component's degree and the number of labels.
The value degree prevents a quartic factor.

For the small-degree estimates of the uniform proof, take the initial
degree-34 quartic interpolant at $t_0$ as well. At most $34\cdot13=442$
points on the degree-13 curve can be off all its common components with
the quartic, after separating the shared factors. More precisely, on a
given irreducible linear or quadratic factor of the cubic either the factor
also divides the degree-34 interpolant, or it carries at most $34\cdot13$
points. In the first case it inherits weight less than $t_0$; the nonlinear
linear and quadratic bounds 184 and 4128 apply. Thus each nonlinear
positive-value-degree factor has at most 4128 points. Parameter-only
factors account for at most 13 labels.

A large head has more than 512 labels and a core of size at least
$t-\lfloor e/512\rfloor$. If at most two heads are large, the total is
bounded by $2(e+1)+3\cdot4128+13<B_0$. With three large heads, the
[core-union count](second-prime-exact-threshold.md#an-upper-bound-for-every-received-pair)
applies. For clarity, each of their cores has at least $0.373n$ sites.
If collinear, the three heads contribute at most
$3n-2(3\cdot0.373n-3d)$ labels. Only the at most 13 parameter exceptions
remain, and the sum is below $B_0$.

If the heads are noncollinear, every selected point belongs to their three
lines, since a point outside has at most $n-3\cdot0.373n+5d<t$
agreements. Write $c_i$ for the three core sizes. The determinant of the
three head pairs gives $\sum_i c_i\le n+2d$. Consequently
\[
 \sum_i\max(0,t-1-c_i)\ \ge\ 3(t-1)-n-2d=2.
\]
Every line has occupancy at most $e+1$. If some $c_i\le t-3$, its
occupancy is at most $1+\lfloor e/3\rfloor$, since its points need
at least three fresh agreements apiece and their fresh sites are disjoint.
The total is then at most $B_0$. Otherwise at least two cores have
$c_i\le t-2$, giving a total at most
$(e+1)+2(1+\lfloor e/2\rfloor)=20k\le B_0$. This proves goodness
at the predecessor.

## The first failure

For $e=10k$ let $t=6k$. Pick $k-3$ common sites and let $H$ be their
vanishing polynomial. Of the remaining sites choose three distinct
points $\alpha,\beta,\gamma$. They belong respectively to both heads
$01$, $02$, $12$. Partition all remaining sites into three private sets
of $5k$ sites each. Each head has $k-3+2+5k=t-1$ defining sites.

Use triples $v=(u_1,u_2,w)$ in the three-dimensional field vector space
to parametrize three scalar quadratic polynomials
\[
 P_0^v(X)=0,\qquad
 P_1^v(X)=(X-\alpha)\big(u_1(X-\gamma)+w/(\gamma-\alpha)\big),\qquad
 P_2^v(X)=(X-\beta)\big(u_2(X-\gamma)+w/(\gamma-\beta)\big).
\]
They satisfy the required pair equalities at $\alpha,\beta,\gamma$.
The two rows of head $i$ will be $H P_i^v,H P_i^{v'}$ for two vectors
chosen below. All six polynomials have degree at most $k-1$.

For an edge $ij$, evaluate $P_j^v-P_i^v$ at $x$ after dividing out its
forced factor at the corresponding double site. In dual coordinates
the resulting linear functionals for $01,02,12$ are respectively
\[
 (x-\gamma,0,1/(\gamma-\alpha)),\quad
 (0,x-\gamma,1/(\gamma-\beta)),\quad
 (-(x-\alpha),x-\beta,1/(\gamma-\beta)-1/(\gamma-\alpha)).
\]
Within each type their projective classes are distinct at distinct
$x$. Their last coordinates are nonzero. After normalizing the last
coordinate to one, the first two types lie on the two coordinate axes,
and the third describes an affine line of nonzero slope. Each pair of
types shares just one point, at their agreed double site: types $01,02$
at $\gamma$, types $01,12$ at $\beta$, and types $02,12$ at $\alpha$.
The equality at each site follows also by substituting the equality of
the two owner polynomials into their differences with the third.

Assign the received rows according to ownership. At a private site each
of the two other heads needs one fresh scalar; at a double site only the
single nonowner does. At common sites none does. The previous calculation
therefore gives $N=2\cdot15k+3=30k+3$ distinct projective functionals
$[L]$. The forced factor of the edge used for any fresh label is nonzero
there, and $H$ is nonzero there too. Set $v'=(0,0,1)$; the last
coordinate of every displayed functional is nonzero. Its projective
normalization is $(a,b,1)$. Take $v=(s,1,0)$. The resulting scalar
is $-(as+b)$. Two distinct affine pairs $(a,b)$ forbid at most one
choice of $s$ by equality of their scalars. There are fewer than
$\binom N2+1$ excluded choices and $|\mathbb F|>3n^2>\binom N2$.
Choose $s$ outside the exclusions. All $N$ scalars are finite and distinct.

For each label the defining sites and its fresh site give $t$ agreements
with the folded polynomial of that head. The $t-1\ge k$ defining sites
uniquely determine the two individual polynomials, and the second row
differs at the fresh site by the choice of $v'$. Hence these are
$30k+3$ distinct actual bad scalars. The two adjacent grid counts and
monotonicity prove the budget claim.

## Below the plateau

At $n=2^{30}$ and rate $1/16$, let $610000000\le e<671088640$ and write $x=671088640-e$. Every pair on every injective domain of characteristic greater than 1744830589 has at most
\[
 C(e,x)=2(e+1)+\max\!\left(197,1+\left\lfloor e/(3x)\right\rfloor\right)
\]
bad scalars. For a prime field with budget $B=\lfloor p/2^{128}\rfloor$ satisfying $C(e,x)\le B\le2013265922$, the first failing count is in $[e+1,\min(671088640,\lfloor B/2\rfloor)]$ at every positive interleaving width. The right endpoint uses two exceptional heads whenever this beats the three-head failure at the plateau endpoint. [Uniform supremum bracket](../../../ArkLib/Research/ProximityGap/Frontier/ThreeHeadDeficitWindow.lean)

The factor cover has at most thirteen exceptions. A first-order interpolant and the terminal quartic meet in scalar degree at most 154 away from their common components. A value-linear component with at least 185 sections therefore inherits the original base-field secant bound. A violation of $2(e+1)+197$ requires three distinct heads with at least 185 labels each. Put $t=n-e$. If the heads are noncollinear and their joint cores have sizes $c_i$, the determinant gives $\sum c_i\le n+2(k-1)$. Thus either two cores have $c_i\le t-2$, or one has $c_i\le t-3x$. Fresh sites for distinct labels on the same head are disjoint. In the first case the two heads together carry at most $e+2$ labels, and in the second case the smaller core's head carries at most $1+\lfloor e/(3x)\rfloor$. If the three heads are collinear, the bound on the number of distinct fresh scalars on and off their core union suffices. [Factor recognition](../../../ArkLib/Research/ProximityGap/Frontier/FiveEighthCubicFactors.lean) · [Joint-core deficit](../../../ArkLib/Research/ProximityGap/Frontier/PlateauThreeHeadPredecessor.lean)

When $q\ge \binom{2(e+1)}{2}$ the two-head construction also gives the lower probability $2(e+1)/q$. Thus from 610,000,000 through 669,955,044 Hamming errors the lower and upper probability bounds differ by at most $197/q$.

For all 119,910,090 budgets from **1220000199** through **1339910288**, the bracket simplifies to $[\lfloor(B-197)/2\rfloor,\lfloor B/2\rfloor]$. Its endpoints are at most 99 Hamming steps apart. This includes 44,657,671 consecutive budgets immediately above the earlier kernel-checked two-head curve. [Simplified bracket](../../../ArkLib/Research/ProximityGap/Frontier/ThreeHeadDeficitWindow.lean)

| Field budget $B$ | First failing Hamming count |
|---:|---:|
| 1,330,000,000 | 664,999,901 to 665,000,000 |
| 1,342,177,280 | 671,078,064 to 671,088,640 |
| 1,350,000,000 | 671,088,612 to 671,088,640 |
| 1,400,000,000 | 671,088,637 to 671,088,640 |
| Every budget from 1,454,025,385 through 1,565,873,493 | 671,088,639 or 671,088,640 |

For the last row take $x=2$. The upper count is the known plateau attack and all pairs are safe at 671,088,638 errors. Deciding the intermediate Hamming step requires a sharper predecessor bound or a matching received pair. [Two-candidate theorem](../../../ArkLib/Research/ProximityGap/Frontier/ThreeHeadDeficitWindow.lean)
