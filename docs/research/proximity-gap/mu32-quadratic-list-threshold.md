# The exact half-rate list threshold on quadratic fields of budget three

Let a field of characteristic $p>2^{58}$ contain a cyclic subgroup of order 32. For the dimension-16 Reed–Solomon code on that subgroup, the largest list at nine errors has **exactly three** words. A ball at ten errors contains **at least four**. The same counts and inequalities hold for every positive finite interleaving width. Consequently, for **every** quadratic field $\mathbb F_{p^2}$ with $32\mid p^2-1$ and $\lfloor p^2/2^{128}\rfloor=3$, the last good integer count is nine, the first failure is ten, and the operational supremum is $5/16$. Indeed the budget forces $p\ge\sqrt3\,2^{64}$.

The [prior length-32 theorem](mu32-list-threshold-large-characteristic.md) used characteristic $p>2^{128}$ for its upper bound. We keep its overlap argument and characteristic-zero census, bounding the norms of equal-degree locator ratios in the real subfield. The new characteristic estimate covers order-32 subgroups which first appear over a quadratic extension. The length in this argument is 32 throughout.

## The real norm

Let $z$ be a complex primitive 32nd root, $K=\mathbb Q(z)$ and $E=\mathbb Q(z+z^{-1})$. For disjoint exponent sets $A,B$ of the same size $d$ put $L_A(X)=\prod_{a\in A}(X-z^a)$ and define $L_B$ likewise. Fix distinct exponents $x,y$ outside the supports. Write $U=L_A(z^x)L_B(z^y)$, $V=L_A(z^y)L_B(z^x)$ and $R=U/V$.

Conjugation sends $z^x-z^a$ to $-(z^x-z^a)z^{-x-a}$. Both crossed products acquire the same multiplier $z^{-d(x+y)-\sum A-\sum B}$. Thus $R\in E$. All prime divisors of $U$ and $V$ lie over 2, since roots of unity are units and the norms of the dyadic chords are powers of two. There is a unique prime over 2 in $K$. Interchange $A,B$ if needed so the valuation of $U$ is at least that of $V$. Then $R$ is integral in $K$, hence in $E$. If $R\ne1$, the nonzero integer $N_{E/\mathbb Q}(R-1)$ is divisible by any odd characteristic in which the two ratios agree: the specialization at a chosen primitive root kills $R-1$, hence its prime ideal on restriction to $E$ divides the principal ideal $(R-1)$. Every odd-characteristic specialization keeps the denominators nonzero. Conversely, an identity in $K$ specializes at every such root. This argument also applies when the root lies in an extension of the prime field.

There is a shorter check of the quadratic-field corollary. Since $R-1$ is real, its absolute norm from $K$ is the square of its absolute norm from $E$. The denominator $V$ has power-of-two norm. The odd part of the norm of $U-V$ is therefore the square of the odd part of the real norm. The [previous degree-seven and degree-eight odd norm bounds](mu32-list-threshold-large-characteristic.md#lifting-a-constant-ratio-of-vanishers) are below $2^{128}$, sufficient by themselves for $p>2^{64}$. The following calculation obtains $p>2^{58}$.

Translate the two centers to $0,h$. An odd change of exponent labels reduces each nonantipodal separation to $h=1,2,4,8$. Representatives of the eight real embeddings are indexed by $t=1,3,\ldots,15$. Write
$$
 c_{t,a}=\frac{|1-z^{ta}|}{|1-z^{t(a-h)}|},\qquad
 |\sigma_t R|=\prod_{a\in A}c_{t,a}/\prod_{b\in B}c_{t,b}.
$$
Bound the absolute real norm by $\prod_t(1+|\sigma_t R|)$. Each of its 256 terms chooses a subset $I$ of embeddings. For that term form one positive weight $w_a=\prod_{t\in I}c_{t,a}$ for each of the 30 allowed sites. The product of the $d$ largest weights divided by the product of the $d$ smallest dominates the term for every pair of supports. The same list of supports includes either valuation orientation. Summing these maxima bounds the norm even though different terms can attain their maxima on different supports.

The [integer probe](../../../scripts/probes/probe_mu32_real_ratio_list.py) reuses the [outward-rounded chord enclosures](../../../scripts/probes/probe_mu32_odd_ratio_norm.py). It rounds lower and upper products separately, sorts their respective endpoints and rounds each positive contribution upward. These are the resulting upper bounds on the **absolute real norm** for a nonzero comparison.

| Degree | Separation 1 | Separation 2 | Separation 4 | Separation 8 |
|---:|---:|---:|---:|---:|
| 7 | 19561580063987177 | 11561597619970768 | 5116980105937572 | 1120639691640870 |
| 8 | 268152960297124166 | 141775658581013095 | 32964912186595142 | 11989060075558410 |
| 9 | 2329184286403090056 | 1492758234415140114 | 207629848481886380 | 112307715542000118 |

The rows lie below $2^{55},2^{58},2^{62}$, respectively. On at least three distinct test sites the nonantipodal pairs form a connected graph, so agreement on the entire set lifts in the indicated characteristic. In particular the [nonic three-fiber exclusion](mu32-list-threshold-large-characteristic.md#a-degree-nine-consequence-on-these-same-sites) holds in characteristic $p>2^{62}$ on this grid.

## Recovering the list counts

If four distinct words lie within nine errors, the [overlap and census proof](mu32-list-threshold-large-characteristic.md#the-list-upper-bound-at-nine-errors) forces either a degree-seven triangle pencil or a degree-eight opposite-edge ratio constant on seven sites. The lifted triangle is excluded by the characteristic-zero census. In the four-cycle case the lifted ratios would force two distinct antipodal completions of the same seven-set. The contradiction gives the upper bound three. The three-word nine-error construction and four-word ten-error construction use integral identities and differences of distinct grid points. They apply in the fields above. For an interleaved list with four distinct words, a linear combination of its coordinates separates all four outside at most six proper hyperplanes, preserving all original agreements. Scalar examples embed at every positive width. [Constructions and projection](mu32-list-threshold-large-characteristic.md#matching-lower-constructions)

For a concrete quadratic example take $p=32075779469025367711$. The factorization $p-1=2\cdot3^{33}\cdot5\cdot577$ and Lucas witness 3 certify primality. Here $p\equiv31\pmod{32}$, so the prime field has no order-32 subgroup. In $\mathbb F_p[i]$ with $i^2=-1$ the probe constructs the primitive root $16629418864431511969+2037220815422007292i$. The actual agreement counts with their respective centers are $23,23,23$ and $22,22,22,24$. The probe checks distinctness, root order, the budget and the certificate for this characteristic.

Run `python3 scripts/probes/probe_mu32_real_ratio_list.py` from the repository root to reproduce the table and the two quadratic-field witnesses with integer arithmetic.
