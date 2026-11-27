# Rational centers with several poles on the quotient grid

On the order-64 quotient of either named prize field, any rational center with three or more distinct poles on the grid has at most **$2^{29}$** messages attaining the full ordinary-root degree bound. Four poles reduce this to **$2^{22}$**. On the order-128 quotient, five poles give the same **$2^{29}$** bound. The smaller production budget is $2^{30}$. These bounds hold at every positive width and for any support size.

For a denominator with exactly $r$ distinct simple roots, all on the grid, and base dimension $b$, put $m=b+r-1$. The following bounds count messages agreeing with the rational center on at least $m$ ordinary quotient sites. The numerator can have degree up to $m$ in each coordinate.

| Quotient order | Base dimension | Rate | Poles | Ordinary agreements | Maximum number of such messages |
|---:|---:|---:|---:|---:|---:|
| 64 | 32 | $1/2$ | 3 | 34 | 421,645,935 |
| 64 | 16 | $1/4$ | 3 | 18 | 25,947,093 |
| 128 | 16 | $1/8$ | 4 | 19 | 192,764,400 |
| 128 | 8 | $1/16$ | 3 | 10 | 7,108,458 |
| 128 | 8 | $1/16$ | 4 | 11 | 328,065 |

Thus this construction falls below both budgets for every $r\ge 3$ at half and quarter rate on the order-64 quotient, every $r\ge 4$ at eighth rate on the order-128 quotient, and every $r\ge 3$ at sixteenth rate on the order-128 quotient. These conclusions also apply to lists obtained by pulling those base messages back to entire fibers of a length-$2^{30}$ domain. Arbitrary centers and production messages with partial-fiber agreement remain open. The existing over-budget production constructions use the distinct choice of a pole at zero, outside the multiplicative quotient. [Rotated-anchor witnesses](rotated-locator-union.md) · [Sixteenth-rate witness](sixteenth-locator-union.md)

## From ordinary agreements to projective locator values

Let the quotient points be $z^j$ for $j\in\mathbb Z/M$, with $z$ of order $M$. Write $A$ for the on-grid poles and $U$ for the other sites. Give each ordinary site the vector symbol $P(z^j)/D(z^j)$, for a nonzero scalar denominator $D$ and vector numerator $P$. A candidate $f$ has degree less than $b$ in every coordinate. More generally than the table, take any $m$ bounding the degrees of all coordinates of $P-Df$. If $f$ agrees at $m$ ordinary sites $T$, there is a constant vector $v$ such that
\[
 P(X)-D(X)f(X)=v L_T(X),\qquad L_T(X)=\prod_{j\in T}(X-z^j).
\]
This follows from division by the monic degree-$m$ locator in every coordinate. If $P$ vanishes as a vector at any pole, evaluation there forces $v=0$. Only the unique possible polynomial identity $P=Df$ can qualify in this case.

Otherwise choose one pole $a_0$ and a coordinate $i$ with $P_i(z^{a_0})\ne0$. Every qualifying message has $v_i\ne0$. Evaluation at the other poles gives
\[
 \frac{L_T(z^a)}{L_T(z^{a_0})}=\frac{P_i(z^a)}{P_i(z^{a_0})}
 \qquad(a\in A).
\]
There are precisely $m$ ordinary agreements since coordinate $i$ already has $m$ roots. Given $T$, the equation at $a_0$ recovers the entire vector $v$, which in turn recovers $f$. It therefore suffices to bound the number of $m$-subsets having any one prescribed vector of ratios. Scaling a multiplicative coset to its subgroup preserves degree and agreement.

## The integer displacement equations

For odd $1\le\ell<M/2$, let $\Phi_\ell(j)$ count the pairs $(t,\sigma)$ with $0\le t<\log_2 M$, $\sigma\in\{1,-1\}$ and $j\equiv\sigma 2^t\ell\pmod M$. Both signs count at the antipode. The order-64 and order-128 unit certificates for the named primes imply the following. If two supports have an equal locator ratio at $a_0,a$, then their incidence difference $w=1_T-1_{T'}$ satisfies
\[
 \sum_{j\in U}\big(\Phi_\ell(j-a)-\Phi_\ell(j-a_0)\big)w_j=0
 \quad\hbox{over }\mathbb Z
\]
for every $\ell$. Canceling common sites reduces the comparison to the disjoint supports used in those certificates. The calculation takes place in the prime subfield, so the implication also holds over its extensions. [Order-64 transfer](mu64-unit-lattice-transfer.md) · [Order-128 transfer](mu128-unit-ellipsoid-transfer.md)

Form the matrix with these rows for all $a\ne a_0$ and an additional all-ones size row. All supports in the class have the same image. Reducing the matrix modulo the auxiliary prime 257 preserves this necessary condition. If $B$ is a column basis, the bits on $I=U\setminus B$ determine a support in the class uniquely. Equal bits there leave a difference supported on independent columns, and $-1,0,1$ are distinct modulo 257. Call $I$ an information set and write $d=|I|$. Every class has size at most $2^d$.

Translation preserves the displacement columns. Multiplying the exponents by an odd unit permutes the primitive rows because $\ell$ is represented up to sign, and changing $a_0$ takes differences of the same rows. The ranks and information-set certificates therefore transfer throughout each affine orbit of pole sets. Adding poles can only decrease nullity. A kernel vector on the smaller ordinary grid extends by zeros to the previous grid, where the differences between any two retained poles are still among the row combinations.

## Degree-sensitive counting

For $0\le L\le 2^d$, let $W(d,L)$ be the least total Hamming weight of $L$ distinct $d$-bit vectors. It is calculated by taking vectors in increasing order of weight, with $\binom di$ available at weight $i$. Suppose $s$ information sets are available and each site occurs in at most $c$ of them. If a projective class has $L$ supports of size $m$, their $s$ injective projections have total weight at least $sW(d,L)$ and at most $cmL$. Applying the same reasoning to the complements yields
\[
 sW(d,L)\le c\min(m,|U|-m)L.
\]
Zero-padding the projected vectors shows one may replace $d$ by any larger uniform upper bound. The average $W(d,L)/L$ is nondecreasing in $L$, giving the table entries by integer binary search.

For triples, the verifier constructs a partition of the columns into two independent sets and extends each to a basis. The complements are disjoint information sets. It checks the ranks and disjointness directly. At order 64 the dimensions are 28 in 30 affine triple classes and 29 in five. At order 128 they are 60 in 62 classes and 61 in six. The two-set inequality therefore uses $(s,c)=(2,1)$. For the 399 quartet classes at order 64, a single rank computation in each gives $d\le22$. An exhaustive order-16 control at both actual primes evaluates all 1,716 six-site locators at the three selected sites and checks the displacement condition on each repeated projective value. [Triple and order-64 verifier](../../../scripts/probes/probe_projective_locator_information.py)

At order 128 all 1,594 quartet classes satisfy $d\le46$. For each quartet the verifier repeatedly selects a column basis giving preference to sites appearing most frequently in earlier information sets. It checks independence of the chosen basis by a second rank calculation and records the actual site loads. Across all quartets, 1,162 certificates use three projections, 420 use five, two use eight and ten use ten. In every case $5c\le2s$, giving the bound $5W(46,L)\le 2\min(m,124-m)L$.

To check all five-site pole sets, first retain the 541 quartet classes with $d\ge30$. These give 68,415 centered quartets after applying the affine symmetries. Every quintet with a remaining four-site restriction of nullity at most 29 already has nullity at most 29 by zero extension. Every other quintet can be moved so that it contains one of the 541 representatives. The verifier adjoins every possible fifth site, tests the five quartet restrictions and takes one representative per surviving orbit. Direct rank calculations on these 4,085 residual quintets give nullity 26 in 3,323 cases, 27 in 712, 28 in 42 and 29 in eight. This proves the uniform $2^{29}$ bound for five or more poles. [Quartet and quintet verifier](../../../scripts/probes/probe_projective_locator_quintets.py)

Run the first verifier with Python 3 and the second with Python 3 and `python-flint`. The finite ranks, projections and populations are executable certificates. The transfer results above supply the field-specific implication from locator equality to the integer equations.

```sh
python3 scripts/probes/probe_projective_locator_information.py
python3 scripts/probes/probe_projective_locator_quintets.py
```
