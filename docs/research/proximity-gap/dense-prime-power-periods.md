# Dense prime-field power periods and the sparse restriction

For every odd prime $k\ge5$, a set of rational primes of lower natural density at least
$6^{-g}/(k-1)$, where $2g=(k-1)(k-2)$, has the following property. Each $p$ in the set splits completely in $\mathbb Q(\zeta_k)$ and, for $H=(\mathbb F_p^\times)^k$, some frequency $b\ne0$ satisfies
\[
\left|\sum_{h\in H}e^{2\pi i bh/p}\right|
\ge \frac{k-2}{2k}\sqrt p-\frac1k .
\]
Consequently the proposed bound $C\sqrt{|H|\log(p/|H|)}$ for every prime and every multiplicative subgroup without a size restriction is false for every fixed $C$. The constructed subgroup has order $(p-1)/k$. This construction does not control its smoothness. The sparse prime-field workbench restricts $|H|^2\le p$. Its dyadic specialization additionally prescribes a power-of-two order. [Formal workbench quantifier](../../../ArkLib/Research/ProximityGap/Frontier/ShawFlatnessSubfieldCounterexample.lean) · [Workbench's quarter-power regime](../../../ArkLib/Research/ProximityGap/PROXIMITY_PRIZE_WORKBENCH.lean)

## Sharp limsup at every fixed index

For each fixed integer $d>2$, Mit'kin's 1982 theorem gives infinitely many primes $p\equiv1\pmod{2d}$ and nonzero multipliers $b$ with $|S_b|\ge(d-1-\eta)\sqrt p$, for every fixed $\eta>0$. For $H=(\mathbb F_p^\times)^d$, the identity $S_b=1+d\eta_b(H)$ gives $|\eta_b(H)|\ge((d-1-\eta)\sqrt p-1)/d$. The usual Weil upper bound for $S_b$ gives the reverse limsup inequality. Thus the limsup of $\max_{b\ne0}|\eta_b(H)|/\sqrt p$ along these congruence classes is exactly $(d-1)/d$. The positive-density statement above gives a different quantitative guarantee. The subgroups in this fixed-index argument eventually have $|H|^2>p$, and their orders need not be powers of two. The primary paper is saved locally as `research/mitkin-character-sums-polynomials-1982.pdf`. [Mit'kin, theorem part 2](https://www.mathnet.ru/php/archive.phtml?jrnid=mzm&option_lang=eng&paperid=6067&wshow=paper)

## The two finite identities

Put $S_b=\sum_{x\in\mathbb F_p}e^{2\pi i b x^k/p}=1+k\eta_b(H)$ and let $C_k$ be the smooth projective Fermat curve $X^k+Y^k+Z^k=0$. In the odd-degree case it is isomorphic to $X^k+Y^k=Z^k$. Orthogonality gives
\[
\sum_{b\ne0}S_b^3 = p(p-1)(\#C_k(\mathbb F_p)-p-1),\qquad
\sum_{b\ne0}|S_b|^2=p(p-1)(k-1).
\]
For the first identity the zero triples form the projective cone. Its cardinality is $1+(p-1)\#C_k$. The zero-frequency term is $p^3$. For the second identity the number of equal-power pairs is $1+(p-1)k$, and the zero frequency contributes $p^2$. In particular
\[
\max_{b\ne0}|S_b|\ge\frac{|\#C_k(\mathbb F_p)-p-1|}{k-1}.
\]
The proof uses $|\sum S_b^3|\le(\max|S_b|)\sum|S_b|^2$.

The signed version reaches the sharp limiting constant. The complete sums are real because $k$ is odd. Their first moment over $b\ne0$ is zero, since $x^k=0$ only at zero. Weight $S_b$ by $(S_b-\sqrt p)^2$. The sum of these weights is $p(p-1)k$, and dividing the weighted first moment by this sum yields
\[
\min_{b\ne0} S_b \le \frac{\#C_k(\mathbb F_p)-p-1-2(k-1)\sqrt p}{k}.
\]
The local Lean kernel checks both moment identities, the projective cone decomposition, and the signed inequality for every split odd exponent. [Finite-field proof](../../../ArkLib/Research/ProximityGap/Frontier/FermatPowerMoment.lean)

## Many primes give a large trace at fixed index

Over $K=\mathbb Q(\zeta_k)$, the cohomology of $C_k$ decomposes into one-dimensional Jacobi-sum characters. The decomposition of its Jacobian and the Hecke characters for its factors are described in §2 of Fité, González and Lario. The normalized Frobenius conjugacy classes of this pure, potentially abelian representation equidistribute in its compact image by Johansson's Corollary 15. Over $K$ the compact group is abelian, each eigenvalue has absolute value one, and the $2g$ eigenvalues come in complex-conjugate pairs. Applying this to the full direct sum places all $g$ chosen representatives jointly in a compact subgroup $G\le(S^1)^g$. No independence assumption about these coordinates is required. [Fité, González and Lario, §2](https://arxiv.org/pdf/1403.0807) · [Johansson, Corollary 15](https://arxiv.org/pdf/1307.6478)

Partition each circle into six half-open arcs of length $\pi/3$. For two independent Haar points $u,v\in G$, the chance that every coordinate of both lies in the same respective arc is at least $6^{-g}$, by Cauchy–Schwarz on the cell probabilities. On this event every coordinate of $uv^{-1}$ has argument strictly between $-\pi/3$ and $\pi/3$. The quotient is Haar distributed. Thus the open subset on which every coordinate has real part greater than $1/2$ has measure at least $6^{-g}$. Equidistribution gives at least this lower density among the prime ideals of $K$. Prime ideals of residue degree greater than one have density zero when ordered by norm. Unramified rational primes supporting the remaining ideals split completely in $K$, and each rational prime accounts for at most $k-1$ prime ideals. The prime ideal theorem therefore gives lower rational-prime density $6^{-g}/(k-1)$.

At these primes the normalized trace is greater than $g$, so $p+1-\#C_k(\mathbb F_p)>g\sqrt p$. The finite inequality gives the asserted period lower bound. With $k$ fixed and $p\to\infty$, the ratio to $\sqrt{|H|\log(p/|H|)}$ has lower limit at least $(1-2/k)\sqrt{k/\log k}/2$ along this set. Taking the odd prime indices $k$ arbitrarily large refutes a uniform $C$ in the unrestricted formulation.

For each fixed $k$, arbitrarily small neighborhoods of the compact identity give split primes for which $(p+1-\#C_k)/\sqrt p$ tends to $2g=(k-1)(k-2)$. The signed inequality then gives $\min_b S_b/\sqrt p\le-(k-1)+o(1)$. The classical Weil bound $|S_b|\le(k-1)\sqrt p$ proves equality in the limit. Thus the limsup over split primes of $\max_{b\ne0}|\eta_b(H)|/\sqrt p$ is exactly $(k-1)/k$. This limiting and density argument uses the cited equidistribution theorem outside Lean.

## Why the same Frobenius argument cannot give a sparse counterexample

Point-count positivity gives $g\sqrt p<p+1$ at every prime used above. Consequently $p\gg k^4$. Yet $n=(p-1)/k$ with $n^2\le p$ requires $k\ge(p-1)/\sqrt p$. These requirements are incompatible as $k\to\infty$. Even transferring by the triangle inequality to a subgroup of order $m\le\sqrt p$ inside $H$ only guarantees a bound of order $km/\sqrt p$ from the displayed period. Here $k=O(p^{1/4})$ and $m\le\sqrt p$, so that guarantee is $O(\sqrt m)$.

There is also a two-sided obstruction. For $k\ge4$, $k\mid p-1$ and $k^4\ge4(p-1)$, Mattarei's projective point-count bound gives $\#C_k<3\,2^{-2/3}k^{4/3}(p-1)^{2/3}$. For $n^2\le p$ its hypotheses hold for all sufficiently large $p$, and
\[
\frac{|p+1-\#C_k|}{(k-1)(k-2)\sqrt p}
\ll p^{-1/2}+\frac{n^{2/3}}{\sqrt p}
\ll p^{-1/6}.
\]
Thus even a fixed nonzero fraction of the maximum normalized absolute trace is arithmetically impossible along a sparse family with $p\to\infty$. The estimate allows smaller traces and does not bound the maximum period from above. [Mattarei, Corollary](https://arxiv.org/pdf/math/0511339)

Montgomery, Vaughan and Wooley use $\log(kp)$ in their conjecture, with the additional classical ceiling $(k-1)\sqrt p$. The construction above is compatible with that statement and with its fixed-index asymptotics. [Montgomery, Vaughan and Wooley](https://www.math.purdue.edu/~twooley/publ/1995%20GSUM.pdf)

## A quantified cubic test inside the sparse dyadic range

For dyadic $n\ge2$ and a prime $p\equiv1\bmod n$, define $R_p=\#\{(x,y)\in H^2:1+x+y=0\}$ for $H=\mu_n(\mathbb F_p)$. The nonzero-frequency cubic and quadratic subgroup moments give the necessary inequality
\[
\max_{b\ne0}|\eta_b|\;\ge\;\frac{|R_p-n^2/p|}{1-n/p}.
\]
Indeed $nR_p$ is the ordered number of zero-sum triples, by scaling the first entry. Orthogonality and subtraction of the zero frequency give $pnR_p-n^3$ and $pn-n^2$ for the two moments. The triangle inequality bounds the first by the second times the maximum. A large $R_p$ would therefore disprove the desired scale at an individual sparse prime.

There is an unconditional aggregate bound for this witness:
\[
\sum_{p\equiv1\bmod n} R_p\log p \le \tfrac12 n^2\log 3 .
\]
Let $U,V$ shift the two coordinates of $(\mathbb Z/n)^2$, and put $D=I+U+V$ on its integral group algebra. The tensor Fourier basis over $\mathbb C$ diagonalizes $D$ with entries $1+u+v$ for $u^n=v^n=1$. A zero would require an equilateral triangle on the unit circle: $|1+u|=1$ implies $u+\bar u=-1$, hence $u^2+u+1=0$. Dyadic order excludes this. Every row of $D$ has three distinct unit entries, so its nonzero integer determinant has absolute value at most $3^{n^2/2}$ by Hadamard. At each split $p$ the same Fourier diagonalization over $\mathbb F_p$ gives nullity $R_p$. Smith normal form yields $p^{R_p}\mid\det D$. Multiplying proves the bound, including finiteness of the primes with $R_p>0$.

For $n=2^{30}$ and $2^{158}<p\le2^{159}$, the minimum logarithmic target is greater than $\sqrt{2^{30}\,128}$. Therefore $R_p>\sqrt{n\log_2(p/n)}$ costs at least $370728$ units. The order-three action in the dyadic zero-triple proof shows every prime with $R_p>0$ costs at least three units. Indeed the set of representations of $1$ has the same size as $R_p$ by negation. Since $3^5<2^8$, the numbers of exceptional primes in these two tests are at most
\[
\left\lfloor\frac{4n^2}{5\cdot158\cdot370728}\right\rfloor=15746253961<2^{34},\qquad
\left\lfloor\frac{4n^2}{5\cdot158\cdot3}\right\rfloor=1945859079505226<2^{51}.
\]
The independently established band count exceeds $2^{122}$, giving exceptional fractions below $2^{-88}$ for exceeding the logarithmic target and $2^{-71}$ for any nonzero cubic return. The same determinant bound holds for all dyadic orders and all split primes. It controls one necessary test for the period upper bound. Its fulfillment at a prime does not control the full maximum. This weighted determinant and its prime count are written proofs. [Order-three orbit](../../../ArkLib/Research/ProximityGap/Frontier/DyadicSidonTriple.lean) · [Split-prime band count](../../../PROGRESS.md)

## Fifth returns and the odd-moment extension

The determinant calculation extends to any odd $r\ge3$ without a complex zero eigenvalue. Write $R_{r,p}$ for the number of $(r-1)$-tuples of subgroup elements with $1+x_1+\cdots+x_{r-1}=0$. The normalized count equals $N_0(H,r)/n$. On $(\mathbb Z/n)^{r-1}$ use $I+U_1+\cdots+U_{r-1}$. A length-$r$ positive sum of complex $n$th roots cannot vanish for dyadic $n$. In detail, the multiplicity polynomial $P(X)$ of its exponents would be divisible over $\mathbb Z$ by $\Phi_n=X^{n/2}+1$. Evaluation at one would force $2\mid P(1)=r$. The row norms are $\sqrt r$, and the split-prime nullity is precisely $R_{r,p}$. Hence
\[
\sum_{p\equiv1\bmod n}R_{r,p}\log p \le \tfrac12 n^{r-1}\log r .
\]
When $r$ is prime and $p\ne r$, each positive $R_{r,p}$ is at least $r$. Indeed cyclic permutation acts freely on normalized tuples, since a fixed tuple would be a geometric progression with ratio an $r$th root in the dyadic group. Such a progression must be constant, and its sum cannot vanish. The repository already has Lean proofs of the odd complex vanishing exclusion and the $nr$ divisibility of the unnormalized count. [Odd zero-sum exclusion](../../../ArkLib/Data/CodingTheory/ProximityGap/OddZeroSumCountVanishCharZero.lean) · [Prime-length divisibility](../../../ArkLib/Research/ProximityGap/Frontier/_DQR4DilationDivisibility.lean)

At $r=5$, $n=2^{30}$, and $2^{158}<p\le2^{159}$, use $5^3<2^7$. At most
\[
\left\lfloor\frac{7n^4}{6\cdot158\cdot5}\right\rfloor
=1962994930484052976862162325308525<2^{111}
\]
split primes can have even one five-term additive zero sum. The exceptional fraction is below $2^{-11}$. Every other split prime in this band has the exact signed nonzero-frequency fifth moment $\sum_{b\ne0}\eta_b^5=-n^5$. The identities for an odd moment allow cancellation between positive and negative real periods.

The finite-prime product bound is now formal over the actual subgroup. The theorem
`split_prime_product_sq_le` has only the prime, splitting, positive dyadic exponent and odd relation length hypotheses. For every finite set of such primes it gives
`(∏ p, p^(returnCount m n p))² ≤ (m+1)^(n^m)`, where the count uses field elements satisfying $x^n=1$. This proves the logarithmic estimate by monotonicity. The Lean kernel verifies the modular Fourier basis, lifting its vanishing eigenvectors to divisible integer columns, characteristic-zero nonvanishing and the integer Hadamard bound. [Kernel proof](../../../ArkLib/Research/ProximityGap/Frontier/OddReturnDeterminant.lean)
