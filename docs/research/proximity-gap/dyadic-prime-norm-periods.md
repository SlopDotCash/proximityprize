# Dyadic Gaussian periods from prime norms

Two sparse prime fields have a nonprincipal subgroup period exceeding twice the binary-log scale. In both cases the domain is a multiplicative subgroup of power-of-two order, as required by Arnon–Boneh–Fenzi Definition 2.12. The second field is in their practical size window. These are finite counterexamples to explicit constants. The existence of some absolute constant, the production order $2^{30}$, and the Reed–Solomon proximity gap remain open in this argument. [Sponsor paper](https://eprint.iacr.org/2026/680)

| Subgroup order $n$ | Prime size | Certified real part | Certified ratio to $\sqrt{n\log_2(p/n)}$ |
|---:|---:|---:|---:|
| 256 | 52 bits | $>223$ | $>2.1$ |
| 1024 | 237 bits | $>990$ | $>2.05$ |

For the first row, $p=4283494302159617$, $g=3800919073425889$ and $b=4275064871947385$. The second has $p=126205134105047729256068842055334737587878534445324289139206048206460929$. Both results use the canonical additive character and the full group $H=\langle g\rangle$. The Lean statements include primality, $n^2\le p$, the exact subgroup cardinality, and $b\ne0$. The second also includes $2^{128}\le p<2^{256}$. [256-element proof](../../../ArkLib/Research/ProximityGap/Frontier/PlasticDyadicPeriod.lean) · [1024-element proof with full numerical witnesses](../../../ArkLib/Research/ProximityGap/Frontier/DyadicLogWitness237.lean)

## Integer proof

For $0\le i<n$, let $a_i$ be the least absolute residue of $bg^i$ modulo $p$. Since $\cos(x)\ge1-x^2/2$, $\cos(x)\ge-1$, and $2\pi^2<20$,
\[
 p^2\Re\eta_b\ge \sum_{i=0}^{n-1}\max(p^2-20a_i^2,-p^2).
\]
In each row the kernel checks that the right side exceeds the claimed integer times $p^2$. It checks $g^{n/2}=-1$ or, equivalently here, $g^n=1$ and $g^{n/2}\ne1$. The primality proofs use complete Lucas certificates. Norms and residue sums can be reproduced independently with `python3 -O scripts/probes/probe_dyadic_prime_norm_period.py`. [Independent exact calculation](../../../scripts/probes/probe_dyadic_prime_norm_period.py)

## Prime norms and a limit of the construction

Let $f\in\mathbb Z[X]$ be monic irreducible, with constant term $\pm1$, degree $d$, and roots $\alpha_1,\ldots,\alpha_d$ away from the complex unit circle. Write $A=\mathbb Z[\alpha]$, $\alpha=\alpha_1$, and $m=2^j$. Suppose $p=|N(1+\alpha^m)|$ is an odd prime. Then $A/(1+\alpha^m)$ has $p$ elements and is the field $\mathbb F_p$. In this quotient $g=\alpha\bmod(1+\alpha^m)$ has order exactly $2m$.

Let $L(v)$ be the coefficient of $X^{d-1}$ when $v\in\mathbb Q(\alpha)$ is written in the power basis. Polynomial interpolation gives $L(v)=\sum_{a=1}^d v(\alpha_a)/f'(\alpha_a)$. In particular $L(A)\subseteq\mathbb Z$. The map
\[
 v\longmapsto \exp\big(2\pi i L(v/(1+\alpha^m))\big)
\]
defines a nonprincipal additive character on the quotient. Indeed the bilinear pairing $L(uv)$ is unimodular on the power basis. Its matrix is zero below the degree-$d-1$ antidiagonal and one on the antidiagonal, with integer entries elsewhere. If the displayed character were trivial, this pairing would imply $(1+\alpha^m)^{-1}\in A$, contradicting its norm $1/p$.

For $0\le i<m$ set $t_i=L(\alpha^i/(1+\alpha^m))$. For every fixed $f$ there are $C_f<\infty$ and $0<\lambda_f<1$ such that
\[
 |t_i|\le C_f(\lambda_f^i+\lambda_f^{m-i})
\]
for all sufficiently large $m$. An embedding inside the circle contributes at most a constant times $|\alpha_a|^i$. An embedding outside contributes at most a constant times $|\alpha_a|^{i-m}$. Consequently $\sum_{i<m}t_i^2=O_f(1)$. The remaining $m$ terms are conjugates because $g^m=-1$. The subgroup of size $n=2m$ therefore has some nonprincipal period with real part $n-O_f(1)$. This argument proves the conclusion at every prime norm, without requiring their infinitude.

For fixed $f$, put $M(f)=\prod_a\max(1,|\alpha_a|)$. The norm product gives $\log_2 p=m\log_2 M(f)+o_f(1)$. Thus along any unbounded sequence of these prime norms, the ratio of the maximum period to the binary-log scale tends to $\sqrt{2/\log_2 M(f)}$. The elementary upper bound $|\eta_b|\le n$ gives the matching upper limit. The first finite row used $f=X^3-X-1$ and $m=128$. The second used $X^{17}+X-1$ at $m=512$; its factor $X^2-X+1$ contributes norm one, leaving the nonreciprocal degree-15 factor. This use of traces is related to homoclinic points for hyperbolic toral automorphisms. [Schmidt](https://arxiv.org/abs/1508.03154)

There is a uniform bound on these **fixed-polynomial limiting ratios**. A reciprocal irreducible $f$ with the stated hypotheses has inverse-paired roots. For even $m$,
\[
 \prod_{\{\alpha,\alpha^{-1}\}}(1+\alpha^m)(1+\alpha^{-m})
 =\left(\prod_{\{\alpha,\alpha^{-1}\}}(\alpha^{m/2}+\alpha^{-m/2})\right)^2.
\]
The quantity inside parentheses is an algebraic integer fixed by the entire Galois group, hence an integer. This gives a square and excludes prime norms. For a nonreciprocal algebraic integer, Smyth proved $M(f)\ge\theta$, where $\theta$ is the real root of $X^3-X-1$. Therefore every limiting ratio above is at most $\sqrt{2/\log_2\theta}$, approximately $2.22$. Infinitely many dyadic prime norms are not established even for the cubic. Composite norms with an uncontrolled cofactor and polynomials varying with $m$ require separate analysis. [Smyth's original theorem](https://doi.org/10.1112/blms/3.2.169) · [Author's account](https://arxiv.org/abs/math/0701397)

## A bound for proper prime divisors

Let $f\in\mathbb Z[X]$ be a fixed monic squarefree polynomial of degree $d$. Write $M=\prod_{f(\lambda)=0}\max(1,|\lambda|)>1$. Suppose $g\in\mathbb F_p^\times$ satisfies $f(g)=0$ and has even order $n$. Put $H=\langle g\rangle$. With natural logarithms, there is a constant $C_f$ such that
\[
 \max_{u\ne0}\Re\sum_{h\in H}e^{2\pi i uh/p}
 \;\ge\; 2\min\!\left(\frac n2,\frac{\log p-2d\log n}{\log M}\right)-C_f.
\]
This applies to a degree-one residue root at every proper prime divisor, including when several residue roots occur. The norm can have an arbitrary cofactor. For a sequence with $\log p/n\to\gamma>0$ the resulting asymptotic lower bound for the period divided by $n$ is $\min(1,2\gamma/\log M)$. Existence of such a sequence for any prescribed $f$ and dyadic orders remains a separate arithmetic question.

Let $A$ be the integral companion matrix that sends $(x_0,\ldots,x_{d-1})$ to $(x_1,\ldots,x_{d-1},-\sum_{i<d} f_i x_i)$. For an integral lift $v$ of $(1,g,\ldots,g^{d-1})$, the lattice $\Lambda=\mathbb Z^d+\mathbb Z v/p$ has determinant $1/p$, and $Av\equiv gv\pmod p$. For any integer $L\ge1$ and $0<\delta<1$, take a symmetric convex body in real eigenvector coordinates of $A$. In each real coordinate use a centered interval and in each conjugate pair use a centered disk, of radius $c_f\delta\max(1,|\lambda|)^{-(L-1)}$. Squarefreeness gives these coordinates. Choose $c_f>0$ small enough that $\|A^i w\|_\infty\le\delta$ for all points $w$ in the body and $0\le i<L$. Its volume in the original coordinates is $V_f\delta^d M^{-(L-1)}$ for some $V_f>0$. When this exceeds $2^d/p$, Minkowski's convex body theorem supplies a nonzero $w\in\Lambda$. Since $\|w\|_\infty<1$, it represents a nonzero $b v/p$ modulo $\mathbb Z^d$. Taking the first coordinate of $A^i w$ gives $\|b g^i/p\|_{\mathbb R/\mathbb Z}\le\delta$ throughout the block. The entropy factor agrees with the usual Mahler-measure formula for toral automorphisms. [Lind, Schmidt and Ward](https://research-portal.uea.ac.uk/en/publications/mahler-measure-and-entropy-for-commuting-automorphisms-of-compact/)

Take $J=n$, $\delta=n^{-2}$ and $L\le n/2$. The $2L$ sites $\pm g^i$ of the block are distinct. At a point with $\|t\|\le\delta$, the normalized Fejér kernel satisfies
\[
 K_J(t)=J^{-2}\Big|\sum_{j=0}^{J-1}e^{2\pi i j t}\Big|^2
 \ge 1-\frac{\pi^2}{3}(J^2-1)\delta^2.
\]
This follows from $\cos z\ge1-z^2/2$ and $J^{-2}\sum_{a,b=0}^{J-1}(a-b)^2=(J^2-1)/6$. Every other site contributes a nonnegative quantity. In the expansion of $\sum_{h\in H}K_J(bh/p)$ only the $J$ diagonal pairs contribute the principal period since $J\le p-1$. If $R$ is the largest real nonprincipal period, then
\[
 \frac{n}{J}+\left(1-\frac1J\right)R
 \ge 2L\left(1-\frac{\pi^2}{3}(J^2-1)\delta^2\right).
\]
Hence $R\ge 2L-O(1)$. The largest integer $L\le n/2$ allowed by the volume inequality is at least $\min(n/2,(\log p-2d\log n)/\log M)-O_f(1)$ whenever a positive such integer exists. In the remaining bounded-right-side range use $R\ge-n/(p-1)\ge-1$, from the mean over nonzero frequencies. This proves the bound. The kernel expansion and extraction of an actual nonzero difference from partial alignment have been verified in Lean for every prime and arbitrary finite sets of sites and frequencies. The companion-matrix volume argument is a written proof. [Lean kernel identity and extraction](../../../ArkLib/Research/ProximityGap/Frontier/FejerPeriodAlignment.lean)

## A necessary common-prime-divisor bound

For every $n$-element domain $D\subseteq\mathbb F_p$ with $n\ge64$, suppose $t$ sites in $D$ have integer lifts of absolute value at most $p/n^2$. There is a nonzero frequency with real period strictly greater than $t-2$. Apply the kernel argument with $J=n$. On each short site every character in the frequency progression has real part at least $1-20/n^2$. Its unnormalized squared sum exceeds or equals $n^2-40$. If every nonzero period were at most $t-2$, its total kernel mass would be at most $n^2+n(n-1)(t-2)$, which is less than $t(n^2-40)$ because their difference is $n(n-2)+(n-40)t>0$. This finite statement is fully verified in Lean. So is the consequence for an integral generator $a$ of order $n=2m$: if $L\le m$ and $a^L n^2\le p$, then a nonprincipal period of the entire subgroup has real part exceeding $2L-2$. [Lean proof](../../../ArkLib/Research/ProximityGap/Frontier/FejerPeriodAlignment.lean)

Suppose a subgroup $H$ of size $n\ge64$ contains $r$ distinct rational primes $q_1,\ldots,q_r$ after reduction. Set $Q=\prod_iq_i$. If $Q^Ln^2\le p$, all $L^r$ products $\prod_i q_i^{e_i}$ with $0\le e_i<L$ have lifts below $p/n^2$. Unique factorization distinguishes them over the integers, and their magnitudes distinguish their residue classes. Lean proves that a nonprincipal real period of $H$ is strictly larger than $L^r-2$. [Formal rank-$r$ bound](../../../ArkLib/Research/ProximityGap/Frontier/FejerPeriodAlignment.lean)

In particular a uniform sparse upper bound $C\sqrt{n\log(p/n)}$ on dyadic subgroups would imply, for every dyadic exponent $N$, that each prime divisor $p$ of $\gcd(2^N-1,3^N-1)$ satisfies
\[
 \log p=O_C\!\left(N^{1/3}\right).
\]
The finite endpoint `common_prime_period` also works directly on $D=\mu_N(\mathbb F_p)$: if $L\ge64$, $6^L N^2\le p$, $N>0$ and $p$ divides both indicated integers, it proves $|D|\le N$ and produces a nonzero frequency with real period greater than $L^2-2$. The first 64 powers of two in $D$ are distinct as ordinary integers modulo $p$, supplying the cardinality required by the kernel argument.

To see the asymptotic implication, let $H=\langle2,3\rangle\subseteq\mathbb F_p^\times$. Its order $n$ divides $N$ since the ambient group is cyclic. Bounded $n$ gives bounded $p$ from $p\mid 2^n-1$. If $p\le n^4$ the conclusion follows immediately. Otherwise $H$ is sparse, and $L=\lfloor\log(p/n^2)/\log6\rfloor$ grows at least as $(\log p)/(2\log6)-1$. Combining the lower bound $L^2-2$ with the proposed upper bound and squaring gives $(\log p)^3=O_C(n)$. With $r$ fixed rational primes the exponent on $N$ becomes $1/(2r-1)$, with constants also depending on those primes. A dyadic sequence of common prime divisors with $\log p/N^{1/3}\to\infty$ would therefore refute every constant in the uniform period upper bound. Existence of this sequence is unresolved. The subexponential gcd estimate of Bugeaud, Corvaja and Zannier concerns the whole gcd and does not supply the required prime divisors. [Original gcd paper](https://doi.org/10.1007/S00209-002-0449-Z)

As a finite check, for $N=2^{26}$ the exact integer gcd is $19515599812384085=5\cdot17\cdot257\cdot65537\cdot13631489$. Divisibility therefore exhausts the candidates for every $2^j$ with $j\le26$. Their respective subgroup orders $|\langle2,3\rangle|$ are $4,16,256,65536,1048576$, so each candidate has $p<n^2$. The integer gcd is reproducible with `from flint import fmpz; n=2**26; print((fmpz(2)**n-1).gcd(fmpz(3)**n-1))`. The order of the subgroup is the least common multiple of the two multiplicative orders.

Ten larger common primes from the published factor list were also checked, with $p=k2^e+1$ and $41\le e\le28285$. Each passes a Proth primality certificate and direct modular checks of the exact orders of 2 and 3. Their generated subgroups all have $n^2>p$. The largest case is $81\cdot2^{28285}+1$, with order exponents 28282 and 28284. These ten checks extend the tested examples past the exhaustive gcd range. The independent checker `con-leche --verified` accepted the 36,543 transitive declarations for the Fejér endpoints together with both finite-field overlap-packing endpoints. [Factor search](https://mathoverflow.net/questions/70548/factors-of-gcd22n-1-32n-1) · [Reproducible integer checks](../../../scripts/probes/probe_dyadic_common_prime_period.py)

The all-moduli simultaneous-order estimate in Corollary 3 of Varjú gives $|\langle 2,3\rangle|/(\log p)^2\to\infty$. On dyadic common divisors this yields $\log p=o(\sqrt N)$. A sequence in the range $N^{1/3}\ll\log p=o(\sqrt N)$ with $\log p/N^{1/3}\to\infty$ is still consistent with that estimate. Pappalardi’s stronger power-of-$p$ conclusion concerns almost all primes. [Varjú, Corollary 3](https://arxiv.org/pdf/2104.04367) · [Pappalardi](https://www.sciencedirect.com/science/article/pii/S0022314X9690044X)
