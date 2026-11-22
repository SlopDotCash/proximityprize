# A modular rank bound for higher-degree locators at the two named primes

At length $2^{30}$ and rate $1/16$, the locator construction on the order-128 quotient gives an over-budget list using nine roots. On **each actual named prime**, increasing the root count to any $10\le m\le128$ gives at most **22,873,536** candidates for any fixed numerator of this construction. On the order-256 quotient, the ceiling is **476,935,528** at degree 19 and **218,073,074** uniformly for degrees 20 through 256. The sums of the individual ceilings over degrees 10 through 128 and degrees 19 through 256, respectively, are both below the smaller budget $2^{30}$, even with a separate numerator allowed at each degree. These are bounds on candidate polynomials, independent of how many auxiliary fibers the received word uses. [Named witnesses and construction](sixteenth-locator-union.md)

Using the prescribed root product as well, the union of both higher-degree ranges and the order-256 degree-18 locators having at most eight unpaired roots has at most **1,062,800,482** words at **83,886,079 agreements** about any received word. This leaves **10,941,342** entries below the smaller budget. Each quotient and degree may use its own fixed numerator and common multiplier.

Let $M=128$ or $256$, let $h=2^{30}/M$, and suppose the nonzero common multiplier $H(X)$ has degree $h-1$. Write $L_T(Y)=\prod_{u\in T}(Y-u)$ for an $m$-subset of $\mu_M$ and fix a monic degree-$m$ numerator $P(Y)$. The construction uses $H(X)Q_T(X^h)$ where $YQ_T(Y)=P(Y)-L_T(Y)$. The code degree bound gives $\deg Q_T\le M/16-1$. Hence the first $t=m-(M/16+1)$ elementary symmetric functions of $T$ are prescribed. Newton's identities prescribe its power sums at frequencies $1,\ldots,t$. Dropping the extra requirement on the constant coefficients can only increase the candidate count. All powers below use the same primitive $M$-th root $\omega$ in the named field.

## Recovering integral identities from finite-field rank

For two candidates write $f_j=\mathbf1_T(\omega^j)-\mathbf1_{T'}(\omega^j)$, $0\le j<M$, so $\sum_j f_j^2\le2\min(m,M-m)$. At a valuation $v$ with $2^v\le t$, put $D=M/2^v$ and fold the coefficients modulo $Y^{D/2}+1$ to get a vector $b$ of length $D/2$. Each output is a signed sum on a disjoint group of $2M/D$ input positions. Thus $\sum b_j^2\le (4M/D)\min(m,M-m)=E$.

The integer multiplication matrix of $b(Y)$ on $\mathbb Z[Y]/(Y^{D/2}+1)$ has rows that are signed permutations of $b$. Hadamard's bound gives $|\det|\le E^{D/4}$. A nonzero vector has nonzero determinant because $Y^{D/2}+1$ is the cyclotomic polynomial of the power of two $D$, irreducible over $\mathbb Q$. Modulo $p$, it splits into distinct linear factors. Evaluation diagonalizes multiplication. For each odd $j\le t/2^v$ the diagonal entry at $\omega^{2^v j}$ vanishes, so the rank drops by at least $c=\lceil\lfloor t/2^v\rfloor/2\rceil$. The nodes are distinct since $t<M$. Therefore $p^c\mid\det$: lift an invertible row operation over $\mathbb F_p$ giving $c$ zero rows to an integral matrix with determinant prime to $p$, and expand the resulting determinant. If $E^{D/2}<p^{2c}$ we conclude $b=0$ over the integers. This is a simultaneous use of several finite-field evaluation constraints, even though the individual coefficient equations were supplied at only one prime. [Related odd-character orthogonality identity](../../../ArkLib/ToMathlib/OddCharacterOrthogonality.lean)

When this test succeeds at every represented valuation, the complex Fourier transform of $f$ vanishes on all frequencies not divisible by $d=2^{\lfloor\log_2 t\rfloor+1}$. Fourier inversion makes $f$ constant on each block $j+(M/d)\mathbb Z$ in $\mathbb Z/M$, of size $d$. Relative to one fixed candidate, only entire empty and full blocks can be exchanged. If there are $k$ full among the exchangeable blocks, both $k\le m/d$ and the number of empty blocks is at most $(M-m)/d$. The number of choices is at most
$$
 \binom{M/d}{\lfloor\min(m,M-m)/d\rfloor},
$$
using symmetry of the binomial coefficient and monotonicity up to the midpoint. At $t>0$ the integer check succeeds at every valuation for $M=128$, $m\ge12$, and for $M=256$, $m\ge23$. In each range the maximum of these ceilings is 4,960.

## Dimensions where the determinant can vanish modulo the prime

Represent an $m$-subset on a group of order $M$ by its signed vector $z_j=\mathbf1_T(\omega^j)-\mathbf1_T(-\omega^j)$ on the $M/2$ antipodal pairs. Its squared norm and support size both equal $w$, the number of singleton pairs. Given $z$, the remaining $(m-w)/2$ pairs are full. Distinct vectors satisfying the same primitive power-sum conditions have squared distance at least $31$ whenever $30^{M/4}<p^c$. This is the same nonzero-determinant test on $z-z'$ with its actual squared length.

For $L$ vectors of squared lengths at most $u$ and pairwise squared distance at least $s>2u$, expanding the sum of the ordered squared distances gives
$$
 L(L-1)s\le 2L\sum_i\|z_i\|^2-2\Big\|\sum_i z_i\Big\|^2\le2L^2u .
$$
Thus $L\le\lfloor s/(s-2u)\rfloor$. [Lean packing inequality](../../../ArkLib/Research/ProximityGap/Frontier/LocatorSignedPacking.lean) In particular for subsets of size $q\le11$ on the order-128 group, fixing their first power sum allows at most
$$
 J(q)=\min\!\left\{\binom{128}{q},\,
 \left\lfloor\frac{31}{31-2q}\right\rfloor\binom{64}{\lfloor q/2\rfloor}\right\}
$$
subsets: there are at most the displayed number of signed vectors before the binomial factor, and at most that binomial number of ways to restore full pairs. Here $30^{32}<p$ at both named primes. This settles $M=128$, $m=10,11$.

For $M=256$, $m=20,21$, the frequencies $1,3$ are both prescribed, so $30^{64}<p^2$ gives the same distance $s=31$. For fixed weight $w$, mark $k$ of the nonzero signed entries. Among vectors with identical marks, removing them leaves squared length $w-k$ and preserves distances. Counting marked vectors in two orders shows that their original number is at most
$$
 C(w)=\min_{0\le k\le w,\,2(w-k)<31}
 \left\lfloor\frac{2^k\binom{128}{k}}{\binom wk}
              \left\lfloor\frac{31}{31-2(w-k)}\right\rfloor\right\rfloor .
$$
Now fix a signed vector. The second power sum leaves a prescribed first power sum for its $q=(m-w)/2$ full pairs on $\mu_{128}$: the singleton contribution is fixed, and $(\omega^j)^2+(-\omega^j)^2=2\omega^{2j}$. There are at most $J(q)$ completions. Summing $C(w)J((m-w)/2)$ over the possible weights gives **34,991,632** and **218,073,074**, respectively. At $m=22$ the three primitive constraints already force the order-256 folded vector to agree integrally, and its at most eleven full pairs are again bounded by $J$. The count permits roots in the spare fibers and allows every root product.

The [integer verifier](../../../scripts/probes/probe_dyadic_locator_degree_caps.py) compares integer powers, counts signed marks, and checks the full-lifting implication against direct finite-field enumeration at small orders. Its totals over degrees are 38,127,884 at order 128 and 275,944,318 at order 256. The order-256 total here covers degrees 20 through 256. The degree-19 argument below extends the total to 752,879,846 over degrees 19 through 256.

## Degree 19 on the order-256 quotient

Here only the first two power sums are fixed. The following finite property of the two named fields supplies the extra constraint. Every zero sum of at most eight signed order-256 roots reduces to the empty sum by antipodal cancellation. Multiplicities are allowed. Write $\zeta$ for a complex primitive 256th root and $g$ for the specified generator in the finite field. The finite property says precisely that an equality between sums of at most four roots on either side lifts under $g\mapsto\zeta$. Indeed any signed sum of length at most eight can be divided into two sums of length at most four by absorbing minus signs into the roots. In characteristic zero $1,\zeta,\ldots,\zeta^{127}$ are a rational basis, so reduction by antipodal cancellation is unique.

To verify the property, rotate a nonempty reduced multiset of at most four exponents so that it contains zero. Among rotations starting just after a largest cyclic gap, use the lexicographically smallest gap sequence. Compute $s=\sum_i g^{e_i}$ for this representative. Two nonzero sums lie in the same rotation orbit exactly when their 256th powers agree in the prime field. The checker tests that all these powers are nonzero and distinct across every representative of every size. Equality for two rotated multisets now forces equality of the representatives and of their rotation factors. A reduced multiset has a free rotation orbit in characteristic zero, since its sum is nonzero and rotation multiplies the sum by a root of unity. The independent expected number of representatives of size $b$ is therefore
$$
 \frac1{256}\sum_{j=1}^b\binom{128}j2^j\binom{b-1}{j-1}.
$$
The factors choose occupied antipodal pairs, their orientations and their positive multiplicities. For $b=1,2,3,4$ the checked counts are $1,128,10{,}923,699{,}136$. The two finite roots in field order are $322599146406626103794850093414153468931889947837$ and $570111643962194518645012562298052832947617858734$. Direct modular powering gives $g^{128}=-1$ and $g^{256}=1$ in each certified prime field. All generators give the same subgroup, and relabeling by an odd power preserves antipodal cancellation. [First primality certificate](../../../ArkLib/Research/ProximityGap/Frontier/_PrizeShapePrimeP30.lean) · [Second primality certificate](../../../ArkLib/Research/ProximityGap/Frontier/_PrizeShapePrimeP30Second.lean)

First count the supports with at most five singleton antipodal pairs. At primitive weight $w=1,3,5$, mark $u=\max(0,w-4)$ of the signed entries. At most four signed roots remain. The first power sum and these marks therefore determine the whole orientation by the short-sum check. Counting marks gives at most $\lfloor2^u\binom{128}{u}/\binom wu\rfloor$ orientations. The prescribed second moment gives at most $J((19-w)/2)$ completions per orientation, by the order-128 argument above. The sum for these three weights is **4,666,368**.

For the remaining supports, let $i=g^{64}$ and partition the roots into 64 blocks $\{r,ir,-r,-ir\}$ where $r=g^j$ for $0\le j<64$. Define the imbalance $s_j$ to be the occupancy of $\{r,-r\}$ minus the occupancy of $\{ir,-ir\}$. The second power sum is $\sum_j s_j g^{2j}$. Thus two distinct imbalance vectors in the same fiber have squared distance at least 31 by the order-128 determinant bound. Let $k$ be the number of entries of absolute value two and $l$ the number of entries of absolute value one. The squared norm is $4k+l$. Marking $a$ signed double entries and $b$ signed single entries gives at most
$$
 V(k,l)=\min_{a,b}
 \left\lfloor
 \frac{\binom{64}a\binom{64-a}b2^{a+b}}
      {\binom ka\binom lb}
 \left\lfloor\frac{31}{31-2(4(k-a)+l-b)}\right\rfloor
 \right\rfloor
$$
possible imbalance vectors. Here $0\le a\le k$, $0\le b\le l$ and the denominator in the inner floor must be positive. This follows from the same squared-distance bound after the marked coordinates have been deleted.

Fix an imbalance vector. Each double block contains one prescribed full antipodal pair. Among the $l$ single blocks, choose $v$ to contain three roots and put one root in every other single block. Each contributes one freely oriented root to the first power sum, since any full pair sums to zero. Among the $64-k-l$ zero blocks choose $h$ to be full. A further
$$
 j=(19-2k-l)/2-v-2h
$$
zero blocks must be active, each carrying one root of each antipodal pair. The other zero blocks are empty. There are $Z=64-k-l-h$ blocks available for these $j$ choices. Only admissible nonnegative counts are used. The primitive weight is $w=l+2j$; retain $w>5$ here.

Two bounds count the possible phases on these sites.

- Fix the $j$ active blocks. The remaining $w$ binary signs form a code of minimum Hamming distance nine. Otherwise subtracting the first power sums and dividing by two gives a zero sum of at most eight roots on distinct antipodal pairs. The short-sum check forbids this. Thus the count, including supports, is at most $\binom Zj H(w)$, with $H(w)=1$ for $w<9$ and $H(w)=\lfloor2^w/\sum_{a=0}^4\binom wa\rfloor$ otherwise, by disjoint Hamming balls of radius four.
- Within an active block the four possible contributions $(\pm1\pm i)r$ are $(1+i)$ times its four possible roots. Put $b=\min(4,j)$ and $e=\min(l,4-b)$. Mark $j-b$ of the active blocks and their phases. Fix the signs on all but a predetermined $e$ of the single blocks. For two completions subtract the primitive sums and divide by $1+i$. Each changed single sign gives $(1-i)$ times one root, a sum of two roots in that single block. The unmarked active phases give a signed sum of at most $2b$ roots. Since $2e+2b\le8$, each term must cancel antipodally. Distinct blocks have disjoint pairs. A changed single sign contributes two roots on distinct pairs in its block, so no such sign changes. The remaining active blocks and phases agree as well. Each support has $\binom jb$ markings, giving the cap $\lfloor\binom Z{j-b}4^{j-b}2^{l-e}/\binom jb\rfloor$.

Use the smaller of these two counts. Multiply it by $V(k,l)\binom lv\binom{64-k-l}{h}$ and sum over $l,v,h$ for each $k$. Adding the earlier charge for the three low weights gives the following fiber caps at both primes.

| Quantity | Candidate cap |
|---|---:|
| Degree 19, all root products allowed | 476,935,528 |
| Degree 20 | 34,991,632 |
| Degree 21 | 218,073,074 |
| Sum for degrees 20 through 256 | 275,944,318 |
| Sum for degrees 19 through 256 | 752,879,846 |

Run the [degree-19 verifier](../../../scripts/probes/probe_dyadic_locator_degree19.py) with Python 3 from the repository root.

~~~sh
python3 -B scripts/probes/probe_dyadic_locator_degree19.py
~~~

It checks the short-sum property at both named primes, exhaustively compares the smaller order-16 construction with direct evaluation, and checks that order eight at $p=17$ fails the short-sum test. The degree-19 result uses a written proof and an exact executable certificate.

Degree 18 permits a larger fiber. Taking nine whole antipodal pairs gives first power sum zero. Cyclic rotation of the 128 pair labels increments their exponent sum by nine modulo 128, so their root products give 128 equally populated classes. Each class has $\binom{128}9/128=148{,}927{,}359{,}625$ different supports. For their common constant coefficient $c$, $P(Y)=Y^{18}+c$ satisfies the numerator requirements on this whole class. A fourth-moment count limits the number of these paired words reaching a given agreement threshold around any received word. [Degree-18 agreement count](antipodal-locator-fresh-energy.md) The unrestricted list-decoding thresholds remain open.

## Both quotients at 83,886,079 agreements

The locator identity at $Y=0$ prescribes $\prod_{u\in T}u=(-1)^mP(0)$. Once the unpaired roots are known, the $q$ full pairs $\{u,-u\}$ are determined by their distinct labels $u^2$. Their product contribution is $(-1)^q\prod u^2$, so the labels themselves have a prescribed product. If the second power sum of $T$ is also given, the label sum is prescribed, since each pair contributes $2u^2$.

Consider first $q\le11$ labels on $\mu_{128}$ with prescribed sum and product. The signed-vector packing bound gives at most $\lfloor31/(31-2q)\rfloor$ orientations. Fix one of them and let $f$ be its number of full pairs. Their labels in $\mu_{64}$ have a prescribed product by the same calculation. After writing the labels as powers of a primitive 64th root this fixes their exponent sum modulo 64. Adding a common shift $c$ to the exponents changes the sum by $fc$. The $64/\gcd(64,f)$ bins in this orbit have equal populations. Their total is at most $\binom{64}{f}$, including when some sites are forbidden by the orientation, since we can first discard those prohibitions. Taking the maximum over $f$, which is determined in each orientation, gives the uniform bound
$$
 J_\times(q)=\min\!\left\{\binom{128}q,\,
 \left\lfloor\frac{31}{31-2q}\right\rfloor
 \max_{0\le f\le\lfloor q/2\rfloor}
 \frac{\gcd(64,f)}{64}\binom{64}{f}\right\}.
$$
For the empty subset use $\gcd(64,0)=64$. This directly bounds degrees 10 and 11 at order 128. At order 256 it replaces $J(q)$ after the unpaired roots have been fixed, including in the preceding proofs for degrees 20 through 22.

At order 256 and degree 19, the named fields also admit the stronger five-term sum certificate. For weights $w=1,3,5,7$, marking $\max(0,w-5)$ signed roots determines the rest from the prescribed first sum. With $J_\times((19-w)/2)$ completions per orientation these four weights contribute at most **1,167,243** candidates. For $w>7$ use the same imbalance-vector count $V(k,l)$. The fixed-support signs now have minimum Hamming distance eleven, because any difference on at most ten signs yields a forbidden signed relation after division by two. In the active-block bound use $b=\min(5,j)$ and $e=\min(l,5-b)$. Division by $1+i$ produces at most $2e+2b\le10$ roots and hence forces the same marked completion. Summing the smaller of this count and the radius-five Hamming-ball count gives **121,407,799** additional candidates. [Five-term certificate](antipodal-locator-fresh-energy.md#eight-unpaired-roots-at-the-same-first-sum)

| Quotient order | Degrees and root restrictions | Upper bound |
|---:|---|---:|
| 128 | 10 | 238,266 |
| 128 | 11 | 357,399 |
| 128 | 12 through 128, summed | 5,324 |
| 256 | 18, at most eight unpaired roots, in the received ball | 721,759,140 |
| 256 | 19 | 122,575,042 |
| 256 | 20 | 17,431,579 |
| 256 | 21 | 200,070,257 |
| 256 | 22 | 357,399 |
| 256 | 23 through 256, summed | 6,076 |
| | **Combined** | **1,062,800,482** |

All rows except degree 18 count admissible candidates even before imposing agreement. At order 256 set $h=2^{22}$. For each received word the degree-18 row counts those attaining at least $20h-1=83{,}886{,}079$ agreements. Summing the rows proves the asserted union bound at that threshold on each designated field, even if a different $P,H$ is chosen for each row and degree. The same count applies to repetitions of these scalar words about an arbitrary interleaved center by projecting on one coordinate. The remaining locator classes include order-128 degree nine and order-256 degree 18 with at least ten unpaired roots. [Degree-18 agreement count and reproduction commands](antipodal-locator-fresh-energy.md#counting-the-fresh-sites-across-a-list)

For individual budgets this union remains within budget down to **83,823,446 agreements on the first field** and **81,367,598 on the second**. Indeed, all higher-degree rows sum to $K=341{,}041{,}342$. If the union contains $B+1$ words at $t$ agreements, at least $B+1-K$ of them occur in the degree-18 row. Its fresh-site bound with $C=2{,}830{,}428$ and $r\le h-1$ common roots gives
$$
 t\le 18h+r+\frac{(256h-r)C}{B+1-K}
 \le19h-1+\frac{(255h+1)C}{B+1-K}.
$$
The second inequality uses $B+1-K>C$. Taking the floor and adding one gives the stated sufficient agreement thresholds. Equivalently, an over-budget list from this union requires at least 989,918,379 errors on the first field and 992,374,227 on the second. These are one-sided bounds for the indicated locator families.

The two Python commands below reproduce the arithmetic. They check all small cyclic product layers at orders 4, 8 and 16 and compare the joint first-sum, second-sum and product bounds against direct enumeration at order 16. The linked C++ verifiers establish the named-field five-term property and the degree-18 incidence input.

~~~sh
python3 -B scripts/probes/probe_dyadic_locator_degree_caps.py
python3 -B scripts/probes/probe_dyadic_locator_degree19.py
~~~
