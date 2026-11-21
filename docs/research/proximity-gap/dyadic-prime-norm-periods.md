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
