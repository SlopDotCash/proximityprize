# Protected roots and lifting vanisher ratios at production length

Let $n=2^{30}$, $h=n/4$ and $H=\mu_n(\mathbb F_p)$ for either named production prime. Fix a generator $g$ of $H$ and a complex primitive $n$th root $\zeta$. A subset of exponents defines the same labeled sites in the two fields. Write $L_A(X)=\prod_{a\in A}(X-a)$ in either field.

For each degree $d=h-1,h+1$ there are disjoint $d$-element sets $A,B$ such that $L_A/L_B$ is constant on all **262,144** sites of $\mu_{2^{18}}$ in the named field and takes at least two values on their complex lifts. With a bound on the reduced degree in place of an exact degree, this obstruction holds on **five million** protected sites. The constructions are existence proofs for each prime separately. The production three-fiber test prescribes a third fiber of size $d$.

## The parity constraint in the complex field

The matrix $\big(\log|1-\zeta^{ur}|\big)_{u,r}$, indexed by odd residues modulo sign in both directions, is invertible. Up to permuting the columns it is a group circulant. The nontrivial character eigenvalues are nonzero by the classical nonvanishing of $L(1,\chi)$ and the prime-power log-sine formula. The trivial eigenvalue is $(\log 2)/2$ by $\Phi_n(1)=2$. Consequently, a product of factors $1-\zeta^r$ with odd $r$ can be a root of unity only if the total exponent at every pair $\{r,-r\}$ vanishes. [Cramer, Ducas, Peikert and Regev, Section 3](https://sites.cc.gatech.edu/fac/cpeikert/pubs/logunit.pdf)

Suppose $R=L_A/L_B$ is constant on three sites with distinct even exponents $x$. Set $w(a)=1_A(a)-1_B(a)$ on exponents. Apply the automorphism $\sigma(\zeta)=-\zeta$. The quotient $R(\zeta^x)/\sigma(R(\zeta^x))$ is independent of $x$. All even-exponent roots cancel, and applying $\sigma$ shifts every odd-exponent root by $n/2$. Write $v(a)=w(a)-w(a+n/2)$ for odd $a$ and put $v(a)=0$ for even $a$. The product left at an even test exponent $x$, up to a root of unity, is $\prod_{a\text{ odd}}(1-\zeta^{a-x})^{v(a)}$. Comparing two test exponents and using the just-proved independence shows that $v(x+i)+v(x-i)$ is independent of $x$ for every odd $i$. It is zero for even $i$.

The additive Fourier coefficient at frequency $b$ of this symmetric sum in $i$ is $2\operatorname{Re}(\zeta^{bx}\widehat v(b))$ with the usual negative sign in the Fourier transform. Antiperiodicity forces $\widehat v(b)=0$ at even $b$. At odd $b$ the three values $\zeta^{bx}$ are distinct. If $\widehat v(b)\ne0$, their images on a circle would lie on a single line of constant real part, which can contain at most two points of that circle. Thus $v$ vanishes. Since $A,B$ are disjoint, both are antipodally symmetric on the odd class. Shifting all exponents by one gives the assertion with the parity classes exchanged.

## Five million protected sites

Choose any antipode-closed set $T$ of $s=5,000,000$ exponents containing at least three even and three odd exponents. There are $M=(n-s)/2=534,370,912$ antipodal pairs in its complement. Form a support by choosing $j=M/2$ pairs and one orientation in each. There are
$$
2^j\binom{M}{j}\ \ge\ \frac{2^{j+M}}{M+1}\ >\ 2^{801556339}
$$
choices. Fix $t_0\in T$ and associate to a support $U$ the tuple $L_U(t)/L_U(t_0)$ for $t\in T\setminus\{t_0\}$. Its entries are nonzero. Since both primes are less than $2^{160}$, there are fewer than $2^{799999840}$ tuples.

Two distinct supports therefore produce the same tuple. Remove their common sites to obtain nonempty disjoint sets $A,B$ of the same degree, at most $267,185,456$. The ratio is constant on $T$ in the named field. If the complex ratio were constant there, three even points in $T$ would force both supports to be antipodally symmetric in the odd exponent class. Three odd points would force symmetry in the even class. Each support has at most one member per antipodal pair.

## Exact degrees at 262,144 protected sites

Set $s=2^{18}$ and $T=\mu_s$, which lies in the even exponent class. Choose the auxiliary prime $q$ from the following table. These primes only enter the counting argument.

| Degree $d$ | Auxiliary prime $q$ | $(d-q)/s$ | Lower exponent for the required number of colors |
| ---: | ---: | ---: | ---: |
| $268435455$ | $63700991$ | 781 | 47775714 |
| $268435457$ | $64749569$ | 777 | 48562147 |

Take a set of $4q$ odd exponents containing at most one representative per antipodal pair. This fits because $4q\le h$. Color every $k=2q-1$ element subset $U$ by its tuple of normalized vanisher values on $T$ in the named field. A color contains two supports $U,V$ with $|U\setminus V|=q$. To prove this, suppose one color contains no such pair. For distinct members its intersections range from $0$ to $2q-2$ and avoid $q-1$, the only integer in that range congruent to $k$ modulo $q$. For each member $U$ form the polynomial over $\mathbb F_q$
$$
1-\left(\sum_{i\in U} Z_i-k\right)^{q-1}.
$$
On the incidence vectors of this color these polynomials give the identity matrix. On Boolean inputs they reduce to squarefree polynomials of degree at most $q-1$. The color therefore has size at most $\sum_{i<q}\binom{4q}{i}$. Weighting the binomial expansion by $1/3$ bounds that sum by $3^q(1+1/3)^{4q}=(256/27)^q$. The total number of subsets is at least $2^{4q}/(2(4q+1))$, since the central binomial coefficient is maximal and its adjacent coefficient is at least half as large. Thus if every color avoided the desired pair, there would be at least
$$
\frac{(27/16)^q}{2(4q+1)}
$$
colors. Using $27^4>8\cdot16^4$ gives the lower exponents in the table. The number of tuples in the named field is less than $2^{160(s-1)}=2^{41942880}$.

Cancel $U\cap V$. The reduced supports have degree $q$ and consist of odd exponents. The parity lemma applied to three even sites of $T$ excludes constancy on the complex lifts, since the nonempty reduced supports are antipode-free. Now append $(d-q)/s$ full $s$-cosets to *each* reduced support. Choose all cosets disjoint from one another and from $T$ in the even exponent class. There is room because $2(d-q)+s\le n/2$. A coset vanisher $X^s-c$ is constant and nonzero on $T$ in both fields. The padded ratio retains the two different constancy conclusions and has exact reduced degree $d$.

## A restriction on full fibers

There is also a necessary condition valid directly in the named fields. Let $A,B,T$ be disjoint, with $|A|=|B|=d$ and $R=L_A/L_B$ constant on $T$. Write $I_a(S)=|S\cap aS|$. For every multiplicative translation $a\in H$, the reduced numerator and denominator of $R(aX)/R(X)$ can be taken monic of the same degree
$$
D=2d-I_a(A)-I_a(B).
$$
Indeed the zero and pole multiplicities are the translated differences of the signed indicator $1_A-1_B$. Their total absolute sum equals $|A\mathbin{\triangle}aA|+|B\mathbin{\triangle}aB|=2D$, including multiplicity two when a zero and pole exchange places. If the quotient is nonconstant, the difference of its two monic polynomials has degree at most $D-1$. It vanishes at zero, where $R(0)\ne0$, and at every site of $T\cap a^{-1}T$. Therefore
$$
I_a(T)\le D-2.
$$
A constant quotient must equal one at infinity and makes both $A$ and $B$ translation-invariant. In a dyadic group neither odd-size set can have a nonidentity period. Consequently any three fibers of size $d=h\pm1$ in a single pencil must satisfy
$$
\sum_{S=A,B,T}(d-I_a(S))\ge d+2\qquad(a\ne1).
$$
Taking $a=-1$ counts elements whose antipode is absent from their own fiber. Some fiber has at least 89,478,486 such elements at degree $h-1$, or 89,478,487 at $h+1$.

The inequalities for all translations still admit triples of site sets. Use the additive vector space $\mathbb F_n$ over $\mathbb F_4$, a primitive $b\in\mathbb F_n$, and a nonzero $\mathbb F_4$-linear functional $L$. Give exponent $i$ the color $L(b^i)$ for $0\le i<n-1$ and leave exponent $n-1$ unused. The three nonzero color classes each have size $h$. For a cyclic shift by $j$, the pairs avoiding the unused site split into two groups with multipliers $b^j$ and $b^{j-1}$, according to whether the indices wrap modulo $n$. For $0<j<n$ neither group contains a contributing pair for multiplier one. If a multiplier $a\in\mathbb F_4^\times$ differs from one, $L(x)=L(ax)\ne0$ is impossible. For $a\notin\mathbb F_4$ the two functionals are independent, since $L((a-c)x)$ cannot vanish identically for any $c\in\mathbb F_4$. There are then exactly $3n/16$ equal nonzero outputs in the whole vector space. Summing over the two groups gives $\sum I_a(S)\le3n/8$ for every nonidentity shift of the exponent cycle. Adding or deleting one site per class increases this quantity by at most six, still below $2d-2$ at either degree. These triples satisfy all the necessary translation inequalities.

The verification script checks the production arithmetic with integers, certifies the auxiliary primes by trial division, and exhaustively checks the translation proof on small dyadic groups. The length-32 lifting estimate and its application have separate certificates. [Arithmetic and finite checks](../../../scripts/probes/probe_production_ratio_lifting.py) · [Length-32 lifting](mu32-list-threshold-large-characteristic.md#lifting-a-constant-ratio-of-vanishers)
