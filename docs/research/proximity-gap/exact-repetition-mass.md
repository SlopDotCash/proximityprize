# Exact dimension-one MCA error over most production radii

Let $n=2^{30}$ and let $q>4n^3$ be the size of a finite field. This includes both named production primes. On any injective domain of size $n$, with dimension one and any positive interleaving width, write $t$ for the required agreement count. For every integer $2^{21}\le t\le n$, the worst-center MCA probability equals $M(t)/q$, where
\[
 M(t)=\max_{1\le h\le\lfloor n/(t-1)\rfloor}
  \left(hL_h+\binom h2+r_h\right),\qquad L_h=n-h(t-1).
\]
Here $r_h$ is the largest integer $0\le r<t$ satisfying $rt-\binom r2\le L_h$. On a real radius $\delta$ with $\lceil(1-\delta)n\rceil=t$ the same formula applies. For $3t>2n$ it simplifies to $M(t)=n-t+1$. Evaluating the maximum uses at most 512 center counts in this range.

| Prime budget | Errors | Maximum bad labels | Centers | Rich lines avoiding all centers |
|---|---:|---:|---:|---:|
| $n$ | 805,306,366 | 1,073,741,822 | 2 | 1 |
| $n$ | 805,306,367 | 1,073,741,826 | 2 | 1 |
| $2n$ | 939,524,094 | 2,147,483,641 | 4 | 3 |
| $2n$ | 939,524,095 | 2,147,483,658 | 4 | 4 |

At the lowest agreement count covered, **2,097,152**, the exact mass is **137,439,051,904**. The first-failure thresholds in the table have separate end-to-end Lean proofs. The whole mass formula is a written theorem with exact-integer interval certificates. [First-prime threshold](../../../ArkLib/Research/ProximityGap/Frontier/RepetitionFirstPrimeThreshold.lean) · [Second-prime threshold](../../../ArkLib/Research/ProximityGap/Frontier/RepetitionSecondPrimeThreshold.lean) · [Certificate verifier](../../../scripts/probes/probe_repetition_mass_curve.py)

## The line arrangement and a matching construction

At width one group the $n$ coordinates by their two received values $(b,a)$, giving weighted points in the affine plane. A bad scalar $g$ requires a line $b+ga=c$ with at least $t$ coordinates and at least two distinct points. Conversely every such line supplies a bad scalar. Indeed the fold is constant on its support, whereas the two rows cannot both be constant there. Distinct directions give distinct labels. For an upper bound select just one line per bad direction. For the matching lower bound construct distinct directions. MCA under positive interleaving equals the scalar MCA. [Canonical event](../../../ArkLib/Extensions/Data/CodingTheory/ProximityGap/Errors.lean) · [Rich-line reduction](../../../ArkLib/Research/ProximityGap/Frontier/RepetitionSecondPrimeThreshold.lean) · [Interleaving equality](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityLedger.lean)

Fix $h$ and write $L=L_h$, $r=r_h$. Place $t-1$ copies of each of $h$ centers and use $L$ light points of unit weight. Choose $r$ nonvertical lines of distinct directions with no three concurrent. For instance $b+ga=g^2$ for distinct $g$ works over every field: three concurrent lines would give three roots of one monic quadratic. Include all $\binom r2$ intersections among the light points. Each line then needs $t-(r-1)$ further light points. For $r=0$ there are no prescribed points; for $r\ge1$ their total number is $rt-\binom r2\le L$. Throughout this range $r<t$. The verifier checks the first integer rejected by the quadratic test.

Choose the centers successively off the prescribed lines. On choosing a new center, its directions to earlier centers and to the prescribed intersection points must be finite, distinct, and different from every direction already used, including the $r$ prescribed directions. For each target point and each forbidden direction exclude the corresponding line through it. Also exclude all lines joining two targets, ensuring the new directions are mutually distinct. Once the centers are fixed, add the remaining light points successively. For each new point forbid the lines through each center in earlier directions, the vertical lines through the centers, the lines through two centers, and all earlier points. If this light point is assigned to a prescribed line, all of those forbidden lines intersect its line in at most one point because every center was chosen off the prescribed lines. One may also exclude the intersection with every other prescribed line at this step.

There are at most $n$ existing points, at most $n$ target centers or intersections, and at most $n^2+n$ assigned or forbidden directions. These restrictions exclude fewer than $4n^3$ lines for an unconstrained point, or fewer than $4n^3$ points on a prescribed line. A union of fewer than $q$ lines cannot cover the plane. Thus the choices exist over the stated field. The $hL$ center–light secants, $\binom h2$ center–center secants and $r$ prescribed light lines all have different bad directions. This attains every candidate in the maximum.

## Weighted upper bound

Fix one line for each bad direction and give the distinct points their coordinate weights. An elementary pair-count bounds by $R=\lfloor n^2/(tc)\rfloor$ the number of chosen lines avoiding all points of weight at least $t-c+1$, for any $1\le c\le t$. Each such line contains $t c$ ordered pairs of coordinates at different points or more. A pair can lie on at most one chosen line. Call the points at least this heavy the centers for the upper bound. Let $h$ be their number and $w$ the number of these centers having weight at most $t-2$. At most $\binom h2$ chosen lines hit two or more centers. Through one center the light sets of its one-center lines are pairwise disjoint. Every such line uses at least one unit of light mass, and a line through a weak center needs at least two. [Weighted incidence lemmas](../../../ArkLib/Research/ProximityGap/Frontier/WeightedRichLinePacking.lean)

Writing $d=c-2$, total light mass is at most $L_h+wd$, since each nonweak center has weight at least $t-1$ and each weak center has weight at least $t-c+1$. Therefore, when $w\ge1$, the entire count is at most
\[
 R+\binom h2+(h-w/2)(L_h+wd).
\]
The weaker bound $R+\binom h2+h(L_h+hd)$ covers any $w$, and zero centers give at most $R$.

Suppose instead that all $h\ge1$ centers have weight at least $t-1$. Then $L=L_h\ge0$. Let $Q$ be the set of distinct light points. Put $D=L-|Q|\ge0$. The total excess of light point weights above one is at most $D$. The one-center lines number at most $h|Q|=h(L-D)$. For any $k$ chosen lines avoiding the centers,
\[
 kt\le L+\binom{k}{2}+(k-1)D .
\]
Indeed, their unweighted incidence count is at most $|Q|+\binom{k}{2}$ because each pair of lines meets in at most one point. Counting excess weight adds at most $kD$.

If $h(t-R+1)\ge R-1$, these lines number at most $r_h+hD$. Otherwise one could take $k=r_h+hD+1\le R$ of them. Set $G(j)=jt-\binom j2$. By definition $G(r_h+1)>L$, and
\[
 G(k)\ge G(r_h+1)+hD(t-k+1)>L+(k-1)D ,
\]
contradicting the incidence bound. Thus the total count is at most $hL+\binom h2+r_h$, the same candidate achieved by the construction.

## Certifying all agreement counts

The verifier partitions $[2^{21},\lfloor2n/3\rfloor]$ into **863 disjoint integer intervals**. For each $[a,b]$ it selects one cutoff $c$ and bounds $R$ by $R_0=\lfloor n^2/(ac)\rfloor$. The function $M$ is nonincreasing: each feasible center count at a larger $t$ remains feasible at smaller $t$, with weakly larger light mass and line capacity in this range. The quadratic root used in the script is always on its increasing branch. In particular $M(b)$ is a lower bound on $M(t)$ throughout the interval.

For each $0\le h\le n/(a-c+1)$, substitute $a$ for $t$ in the upper bounds on light mass. The verifier either handles every $w$ with the weaker count, or checks the sharp weak-center bound against $M(b)$ for every $1\le w\le h$. For the latter check, twice the one-center contribution is a concave quadratic in $w$. Its maximum over integers in $[1,h]$ is bounded by checking the two clipped integers straddling the vertex. When a strong-center case remains possible the verifier checks $h(a-R_0+1)\ge R_0-1$, which proves the symbolic strong-center bound throughout the interval. Zero centers are checked directly. All tests use integer arithmetic. [Run the verifier](../../../scripts/probes/probe_repetition_mass_curve.py)

For $3t>2n$, every two chosen lines share a point since $2t>n$. If at least three chosen lines were nonconcurrent, some triple would have no common point. Every coordinate could then count at most twice in that triple, contradicting $3t>2n$. Thus all chosen lines pass through one point whenever there are at least two. If its weight is $z$, their remaining point sets are disjoint and nonempty. The count is at most $(n-z)/\max(1,t-z)\le n-t+1$. A single center of weight $t-1$ with the rest on distinct directions attains this value. At most one center fits in the maximum for $3t>2n$ at this length, and its light-only contribution is zero. This also covers $t=n$.
