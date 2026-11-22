# The sharp dimension-one threshold at the second designated prime

Write $u=2^{27}$ and $n=8u=2^{30}$. At dimension one the last safe error count is **939,524,094** and the first failure is **939,524,095** on every injective evaluation domain at the second designated prime. The safe real radii are those below $939524095/1073741824$. The proof below gives a uniform upper bound of $2n$ at the predecessor and constructs $2n+6$ bad scalars at the next count. At dimensions two through $2^{26}$ the first failure is instead 715,827,882. [End-to-end Lean classification](../../../ArkLib/Research/ProximityGap/Frontier/RepetitionSecondPrimeThreshold.lean) · [Higher-dimensional comparison](../../../ArkLib/Research/ProximityGap/Frontier/TerminalDimensionThreshold.lean)

Two received words on a repetition code give points $(a_i,b_i)$ of the affine plane, with one unit of weight for each coordinate. Merge coincident points and write $w(P)$ for the resulting multiplicities. A bad scalar $z$ at agreement count $t$ has a line $a+zb=c$ of weight at least $t$ containing at least two distinct received points. Conversely such a line supplies a witness: its folded word is constant there, and the two original words cannot both be constant on the full line support. Select one line for each bad scalar. Two selected lines have at most one point in common. [MCA definition](../../../ArkLib/Extensions/Data/CodingTheory/ProximityGap/Errors.lean)

## Predecessor safety

Set $t=u+2$. Call a point heavy if its weight is at least $t-511=u-509$. There are at most eight heavy points. Write $s$ for their number, $L$ for the total weight outside them, and $R$ for the number of selected lines with no heavy point.

Each line counted by $R$ contains at least $512t$ **ordered** pairs of coordinates with distinct points. Indeed its total weight $W$ is at least $t$, and after selecting the first coordinate at most $t-512$ coordinates are unavailable for the second. Distinct selected lines never use the same pair. Consequently $R\le n^2/(512t)<u/8$.

At most $s(s-1)$ selected lines contain two or more heavy points, by assigning an ordered pair of distinct heavy points to each such line. For each fixed heavy point $P$, the light supports of the lines containing $P$ as their only heavy point are disjoint and nonempty. Their number is at most $L$. If $w(P)\le t-2$, each needs at least two units of light weight and their number is at most $L/2$.

If $s\ne4$, the total is at most $R+s(s-1)+sL$, where
$$sL\le s(8-s)u+509s^2\le15u+509\cdot64.$$
This is below $16u$. If $s=4$ and one of the four has weight at most $t-2$, the upper bound becomes $R+12+7L/2$, with $L\le4u+2036$. This also lies below $16u$.

It remains to treat four heavy points of weights at least $t-1$. Then $L\le4u-4$. If one light point $Q$ has weight at least $u/32$, there is at most one selected line through both $Q$ and each fixed heavy point. The other lines through that heavy point as their only heavy point need different light points outside $Q$. Thus the total count is at most
$$R+12+4(1+L-u/32)<16u.$$

If every light point has weight below $u/32$, there are at most four selected lines with no heavy point. Otherwise take five of them. Their total weight is at least $5t$. Their union has weight at most $L$. Each added line overlaps every previous line in weight at most $u/32$, so even the loose bound $5t\le L+25u/32$ gives a contradiction. All selected lines now number at most $4+12+4L\le16u=2n$. This proof works in every field.

## Failure at the next count

Set $t=u+1$. Use $u$ copies of each of the four parabola points $(a^2,a)$ with $a=1,2,4,8$. For each $1\le j\le4u$, add one point with $a=16j$. Joining a centre to a singleton gives the bad scalar $-(a+16j)$. The four possible residues modulo 16 distinguish the centres, and within a residue the singleton is determined. The six centre-pair sums $3,5,6,9,10,12$ are distinct and below every centre–singleton sum. The characteristic of the second prime exceeds $64u+8$, so all these distinctions survive reduction. Each centre–singleton line has at least $u+1$ coordinates and each centre–centre line has at least $2u$.

The resulting $16u+6$ bad scalars exceed the integer field budget $2n$. The two adjacent counts determine the supremum. Scalar MCA equality under interleaving gives the same classification at every positive width. [Adjacent grid theorem](../../../ArkLib/Research/ProximityGap/Frontier/_MCAAdjacentFloorExactPin.lean) · [Interleaving stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)

## Two centers at the first prime

Let $u=2^{28}$ and $n=4u=2^{30}$. On every injective domain at the first designated prime and at every positive width, the last safe number of errors is **805,306,366** and the first failure is **805,306,367**. Hence the closed-ball MCA error is within tolerance exactly at radii $\delta<805306367/1073741824$. [Operational theorem](../../../ArkLib/Research/ProximityGap/Frontier/RepetitionFirstPrimeThreshold.lean)

At the predecessor take $t=u+2$ required agreements. A point of weight at least $t-511$ is heavy. Let $h$ be the number of heavy points and $L$ the mass outside them. Then $h\le4$. The weighted pair count bounds the number of lines through no heavy point by $R=\lfloor n^2/(512t)\rfloor$. For $h\ne2$, summing this bound, $h(h-1)$ lines through at least two heavy points, and at most $h(n-h(t-511))$ remaining lines gives at most $n$. For $h=2$, if one heavy weight is at most $t-2$, lines through that point need two units of light mass apiece, so the one-heavy contribution is at most $L+L/2$. This also gives at most $n$ lines.

If both heavy weights are at least $t-1$, then $L\le2u-2$. A light atom of weight at least $2^{23}$ reduces the number of distinct light points to at most $L+1-2^{23}$, leaving at most $n$ lines in total. Otherwise three rich lines avoiding the heavy atoms would require $3t\le L+9\cdot2^{23}$, an integer contradiction. The total is then at most $2+2+2(2u-2)=n$. The same numerical certificate theorem checks the four-center second-prime bound with its own parameters. [Generic weighted packing certificate](../../../ArkLib/Research/ProximityGap/Frontier/WeightedRichLinePacking.lean)

At $u+1$ required agreements, use $u$ copies of each parabola parameter 0 and 1, and one copy of each parameter $2,4,\ldots,4u$. The pair of received rows is $(a^2,a)$. The secant from center $i\in\{0,1\}$ to singleton $2j$ gives bad scalar $-(i+2j)$, and the secant between the centers adds $-1$. The $4u+1$ sums are distinct modulo the prime. The polynomial degree bound is one, so the two different parameter values on each support rule out a joint explanation by two constants. More generally $m\ge2$ centers repeated $u$ times plus $s$ singletons give $ms+1$ bad labels at $u+1$ agreements whenever $p>m(s+1)$. [General construction](../../../ArkLib/Research/ProximityGap/Frontier/RepeatedParabola.lean)
