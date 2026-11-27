# Both prize thresholds on the sixteen-point subgroup of $\mathrm{GF}(17^{32})$

Let $F=\mathrm{GF}(17^{32})$ and let the evaluation domain be any multiple of its subgroup of order sixteen. At tolerance $2^{-128}$, the budget is $\lfloor17^{32}/2^{128}\rfloor=6$. The table gives the first **failing** closed-ball error count at every positive interleaving width. Dividing an entry by sixteen gives the operational supremum. Its predecessor is the last passing integer error count.

| Rate | Dimension | MCA | List decoding |
|---|---:|---:|---:|
| $1/2$ | 8 | 4 | 6 |
| $1/4$ | 4 | 6 | 9 |
| $1/8$ | 2 | 6 | 12 |
| $1/16$ | 1 | 6 | 14 |

Scaling the input variable reduces the domain to $\mathbb F_{17}^{\times}$. Choosing a basis identifies width-$w$ list decoding over $F$ with scalar list decoding over the extension of degree $w$, preserving agreement at every site. The half-rate upper bound below applies to every extension of the prime subfield. At width one and at higher widths the failure witnesses already have coefficients in the prime subfield. [Field, subgroup and budget in Lean](../../../ArkLib/Research/ProximityGap/JohnsonPrimePowerDomain.lean) · [Scalar extension](../../../ArkLib/Research/ProximityGap/Frontier/ListScalarExtension.lean)

## The half-rate maximum at five errors

The exact maximum at five errors is **six**. This upper bound works on every injective sixteen-point domain. Suppose seven words agree with one center at eleven or more sites each. The site multiplicities $a_x$ then have sum at least 77. The integer inequality $\binom{a_x}{2}\ge4a_x-10$ gives at least $4\cdot77-16\cdot10=148$ pairwise agreements. The sum is at most $7\binom72=147$ since two distinct words agree at most seven times. In exponent order $x_i=3^i$, one center in the prime field has six words at five errors and ten at six errors. Its six-word sublist attains the universal bound. Lean checks the bound and both lists on every extension. [Lean proof](../../../ArkLib/Research/ProximityGap/Frontier/SixteenPrimeSubfieldLists.lean)

### A second calculation over all extension fields

A finite calculation also gives the smaller maximum of three when the pivot error is projectively nonrational. Call the index set $D=\mathbb F_{17}^{\times}$ and the symbol field $K\supseteq\mathbb F_{17}$. Distinct degree-below-eight messages differ on at least nine sites. A list with two or more words therefore includes one at distance exactly five. Subtract this codeword from the center so that the zero word is in the list. Let $A$ be the five nonzero sites of the new center $u$. Scaling the whole list lets us treat its five nonzero values on $A$ as one projective point.

For another codeword $f$, let $B$ be its exact error support against $u$. Then $|A\cup B|\ge9$, and $f$ vanishes off $A\cup B$. Write $L(X)=\prod_{x\notin A\cup B}(X-x)$. The possibilities are as follows.

- If $|B|=4$, then $B$ is disjoint from $A$ and $f=cL$ for $c\ne0$. There is one projective choice for $u|_A$, represented by $L|_A$.
- If $|B|=5$ and $A\cap B=\{j\}$, again $f=cL$. After scaling by $c$, the values of $u$ on $A-\{j\}$ equal the values of $L$. Its value at $j$ can be any element except $0,L(j)$. This describes the usable points on the line spanned by $L|_A$ and the coordinate vector at $j$. The direction with multiplier $c=0$ also drops out.
- If $|B|=5$ and $A\cap B=\varnothing$, then $f=L(a+bX)$. This gives the line spanned by $L|_A$ and $(XL)|_A$. The linear factor must be nonzero at every site of $A\cup B$, which excludes exactly the corresponding rational directions.

Each permitted point gives one codeword for the specified $B$, since the eleven or twelve agreeing sites determine the polynomial. Each word has a unique exact support $B$. Adding one for the zero word and counting the permitted supports therefore gives the actual list size. This also accounts for all distinct words in the case of coincident projective lines.

All these lines and excluded points are defined over $\mathbb F_{17}$. Two distinct lines defined over the base field that meet after extension have a base-field point as their unique intersection, by linear elimination. For a projective point outside the base field that supplies another word, the list size is consequently one plus the number of supports giving the *same* line. Each such line has an allowed nonrational point over every proper finite extension. For a rational point the verifier checks each exact-support condition directly. Rotations and inversion preserve the code up to permuting and rescaling symbols: inversion sends $f(X)$ to $X^7 f(1/X)$. These symmetries reduce the $\binom{16}{5}=4368$ possible pivots to 147 orbits.

| Evaluation points | Pivot size | Pivot orbits | Maximum at a rational point | Maximum at a nonrational point on a listed line |
|---:|---:|---:|---:|---:|
| 8, dimension 4 | 3 | 5 | 7 | 3 |
| 16, dimension 8 | 5 | 147 | 6 | 3 |

The first row is an independent check against the known octagon maximum. In exponent order $x_i=3^i$, the center
$$
(1,1,11,0,0,0,0,0,12,0,4,0,0,0,0,0)
$$
has six words at five errors and ten at six errors. The verifier checks both counts again by interpolating through every eight-site subset and evaluating each distinct result at all sixteen sites. Both calculations give first failure at six. [All-center census and interpolation check](../../../scripts/probes/probe_sixteen_point_list_lines.py) · [Octagon control](syndrome-flat-list-profile.md) · [Half-rate witness in Lean](../../../ArkLib/Research/ProximityGap/Frontier/SixteenPrimeSubfieldLists.lean)

## The other three list counts

At quarter rate, six distinct polynomials with eight or more agreements per word would give at least 48 word-site incidences. If $a_x$ counts the words agreeing at $x$, then $\binom{a_x}{2}\ge2a_x-3$, so the sum of pairwise agreements is at least 48. Two distinct cubics agree at most three times, giving at most $3\binom62=45$. Thus every list has at most five words at eight errors.

At nine errors take $y(x)=x^5(1+5x^8)$ in the prime field. The polynomial $f(X)=3+12X+11X^2+8X^3$ agrees at exponents $1,4,5,8,9,10,15$. For every $t\in\mu_8$, the cubic $t^{-5}f(tX)$ has the same number of agreements since $y(tx)=t^5y(x)$. Their constant terms $3t^{-5}$ are all distinct. This single center thus supplies eight words. At eighth rate the established four-by-four grid proof gives list size at most six at eleven errors and exhibits eight lines at twelve. At sixteenth rate all messages are constant. At thirteen errors each qualifying symbol occupies at least three sites, permitting at most five. At fourteen errors eight symbols can occupy two sites apiece. [Quarter-rate orbit in Lean](../../../ArkLib/Research/ProximityGap/Frontier/SixteenPrimeSubfieldLists.lean) · [Eighth-rate proof](../../../ArkLib/Research/ProximityGap/JohnsonPrimePowerList.lean) · [Constant codes](../../../ArkLib/Research/ProximityGap/DimensionOneList.lean)

## The four MCA counts

At half rate and three errors, the cubic apolar bound with $(n,k,e,d)=(16,8,3,7)$ gives $\max(4,3(\lfloor3/3\rfloor+1))=6$ bad scalars. At four errors the prime-subfield example has fifteen bad scalars on this very subgroup. Each persists over $F$: joint interpolation on a fixed witness set is a linear system over $\mathbb F_{17}$, whose consistency is preserved and reflected by field extension. The fold polynomial also extends. At dimensions $k=1,2,4$, the cubic spike theorem gives first failure at the budget $B=6$. Indeed $k+2B\le16$, $3k+2B<37$ and $3\mid B$. The affine-line MCA stability theorem transports these answers to every positive width. [Cubic apolar bound](../../../ArkLib/Research/ProximityGap/Frontier/CubicApolarExtremum.lean) · [Fifteen-label witness in the prime field](../../../ArkLib/Research/ProximityGap/Frontier/SmoothQuinticSeventeen.lean) · [Cubic spike theorem](../../../ArkLib/Research/ProximityGap/Frontier/CubicSpikeBudgetBoundary.lean) · [MCA stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)

The agreement bounds and the explicit failure lists suffice for both half- and quarter-rate thresholds in Lean. Run `python3 scripts/probes/probe_sixteen_point_list_lines.py` from the repository root to reproduce the independent projective-line census and direct interpolation checks. These are sixteen-point results. The separate production table records the length-$2^{30}$ questions. [Production table](full-prize-review.md)
