# The second-prime eighth-rate attack at 679,477,248 errors

On the second named prime at length $n=2^{30}$ and dimension $k=n/8$, a single received pair has at least **2,148,807,811 distinct MCA-bad scalars at 679,477,248 errors**. The budget is 2,147,483,648. This lowers the previous upper bound by one error at every positive width. The construction below uses all $k$ possible intersections of a fourth head with the line containing the first three heads. Lean verifies the actual finite set of bad scalars, its mass for every dimension from 134,217,728 to 394,264,575, and the eighth-rate operational supremum bound at every positive interleaving width. [Lean endpoint](../../../ArkLib/Research/ProximityGap/Frontier/EighthTransverseAttack.lean) · [Relative maps and overlap constants](../../../ArkLib/Research/ProximityGap/Frontier/EighthTransverseMobius.lean) [Executable certificate](../../../scripts/probes/probe_eighth_transverse_mobius.py) · [Earlier upper bound](smooth-four-head-attack.md)

Lean also verifies the allocation on the actual billion sites. Writing each exponent as $j+32r$ reduces the counts to 32 intervals with at most one cut apiece. Each of the four defining cores has 394,264,575 sites, the common locator has 33,554,430 distinct roots, and the 16 map sources have total cardinality 2,239,758,337 before removing poles. Every scheduled target lies outside its defining core. The physical-site and variable-fiber tests use the same tags as the Python allocation. [Physical-site certificate](../../../ArkLib/Research/ProximityGap/Frontier/EighthMobiusSites.lean)

## Four balanced defining cores

Write $s=n/32=33,554,432$, take the named generator $g$ of order $n$, and put $t=X^s$. Write $H_j$ for the coset with $t=(g^s)^j$, so $|H_j|=s$. Take the two cubic polynomials $P,Q$ from the existing sixteenth-root identity with their scales chosen so that $P=Q$ on the third triple. On the thirty-two quotient sites, the zeros of $P$ have indices $0,2,16$, the zeros of $Q$ have indices $4,18,20$, and the equalities $P=Q$ have indices $6,10,14$. The nine fibers are disjoint. Write $R=Q/P$ off the first triple. [Cubic identity](smooth-four-head-attack.md#an-upper-bound-across-lengths-and-field-budgets)

Let $u=g$, $v=g^3$. Choose $s-2$ common coordinates in $H_{31}$, with monic vanisher $J$. The three heads $(Xf_i,f_i)$ use $f_0=0$, $f_1=L=JP(X^s)$ and $f_2=JQ(X^s)$. Choose $b,d$ so $b+du=R(u^s)$ and $b+dv=R(v^s)$. The two values are distinct and neither is 0 or 1. For the fourth head use
\[
 B_3=L(b+dX),\qquad A_3=XB_3-dL(X-u)(X-v).
\]
Here $L$ has degree $k-2$. The degree-$k$ terms in $A_3$ cancel, so all eight row polynomials have degrees below $k$. The fourth head agrees with head 0 at the $k-2$ zeros of $L$ and with head 2 at $u,v$.

Receive the common value at the $s-2$ common sites, the repeated value on the nine pair fibers, and head 2 at $u,v$. Assign each triple head $p_0=19s/4+1$ private sites, counting $u,v$ in head 2's private sites. Give the fourth head $q_0=31s/4-1$ further sites. Every site now has an owner. Choose the $p_0-2$ further private sites for head 2 and the $q_0$ fourth-only sites inside the thirteen cosets indexed by
\[
 5,7,8,9,11,12,13,15,17,19,21,22,23.
\]
They have $13s$ sites and the assignment needs $25s/2-2$. The remaining ordinary sites supply exactly $p_0$ to each of heads 0 and 1. Each triple defining core has $s-2+6s+p_0$ points. The fourth has $k+q_0$. All four cardinalities equal $C=47s/4-1=394,264,575$.

## Folded agreement and the fifteen possible poles

At every triple-owned noncommon coordinate, a distinct triple head gives the fresh label $-x$. At every triple-owned coordinate outside the $k$ defining overlaps, use the fourth head as the foreign head. At every fourth-only coordinate, use each of the three triple heads. This schedules
\[
 (n-q_0-(s-2))+(n-q_0-k)+3q_0
   =2n+11s/4+1=2,239,758,337
\]
fresh incidences.

In the latter two cases $L(x)\ne0$. Put $c=f_i(x)/L(x)$. This equals 0 or 1 for the first two heads, and equals $R(x^s)$ for head 2. On the $Q=0$ and $P=Q$ roots, a double owner can be represented by head 0 or head 1 respectively. Thus head 2 contributes its variable $R(x^s)$ only at the thirteen specified cosets. If $h=(c-b)/d$, the scalar equating the two folds is
\[
 Z_h(x)=-x+\frac{(x-u)(x-v)}{x-h}
       =\frac{(h-u-v)x+uv}{x-h}.
\]
At $x=h$ remove the incidence. There are at most fifteen such losses since there are fifteen values of $c$. Every remaining incidence has unequal second row values and an actual folded agreement outside the corresponding defining core. Polynomial uniqueness on that core makes its label MCA-bad at $n-C-1$ errors.

The named-field evaluation shows that the fifteen $c$'s are distinct and avoid $R(u^s),R(v^s)$. Each $Z_h$ is therefore a bijection of the projective line. All sixteen maps, including $x\mapsto-x$, take $u,v$ to $-u,-v$. They are distinct, since each fractional map has a different pole and the linear map has none at finite $x$. The relative transformation between any two fixes $u,v$. It cannot be a scaling, since a scaling fixing $u\ne0$ is the identity. A scaled reciprocal fixing both would give $u^2=v^2$, whereas $u\ne\pm v$. The certificate also directly checks that every relative matrix has all four entries nonzero.

## Counting collisions in the named field

If one map is used on a coset of size $N$ and another on a coset of size $M$, normalize the two cosets to subgroups by scaling. The relative transformation has the form $(aX+b)/(cX+d)$ with $a,b,c$ nonzero and $ad-bc\ne0$. The normalization preserves these conditions. Image intersections are therefore bounded by the number of points $x^N=1$ satisfying $(x+b/a)^M=(c/a)^M(x+d/c)^M$. Its zero and pole are distinct, the zero is nonzero, and regular graph points meet neither. For positive integer parameters $A,B,C',D$, the checked rectangular Stepanov theorem bounds this cardinality by
\[
 \left\lfloor\frac{A-1+N(C'-1)+M(B-1)}{D}\right\rfloor
\]
when $A\le N$, $AC'\le M$, $A-1+N(C'-1)<p$, $D\le p$, and $D(A+2(D-1))<BAC'$. [Lean subgroup theorem](../../../ArkLib/Research/ProximityGap/Frontier/MobiusSubgroupBound.lean)

| $N$ | $M$ | $A$ | $B$ | $C'$ | $D$ | Pair bound |
|---:|---:|---:|---:|---:|---:|---:|
| $2^{30}$ | $2^{30}$ | 1,322,342 | 1,621 | 812 | 659,139 | 3,960,117 |
| $2^{30}$ | $2^{25}$ | 419,430 | 5,101 | 80 | 205,908 | 1,243,048 |
| $2^{25}$ | $2^{25}$ | 131,072 | 509 | 256 | 65,279 | 392,196 |

Three maps are used on subsets of the full subgroup and thirteen more on subsets of one small coset each. Each map contributes at most one incidence per input, and each is injective on its regular inputs. Subtracting all pair intersections overcounts the loss from repeated labels, since $m-1\le\binom m2$. The total loss is at most $3(3,960,117)+39(1,243,048)+78(392,196)=90,950,511$. After removing fifteen possible poles there remain at least **2,148,807,811** distinct bad labels. Scalar-to-interleaved stability gives the same lower bound divided by the field size at every positive width. [Interleaving theorem](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityLedger.lean)

At lengths 128, 256, and 512 on subgroups of the same production field, direct evaluation witnesses 268, 535, and 1,069 distinct bad labels at 81, 162, and 324 errors. These counts check the smaller constructions independently of the subgroup-intersection estimates. The unrestricted first failing count for the production code remains open.

For any sixteen input subsets with the specified total incidence count, Lean now removes all finite poles, proves per-map injectivity, and bounds intersections of the literal images. The last thirteen subsets need only belong to their prescribed index classes modulo 32. The resulting union contains at least 2,148,807,811 labels. [Actual collision and union theorems](../../../ArkLib/Research/ProximityGap/Frontier/EighthTransverseCollisions.lean)
