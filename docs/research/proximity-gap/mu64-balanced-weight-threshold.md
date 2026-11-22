# Sharp balanced locator weights on the two named order-64 grids

Fix matched primitive roots $z$ of order 64 in a named prime field and in $\mathbb C$. Let $w:\mathbb Z/64\to\mathbb Z$ satisfy $\sum_jw(j)=0$ and put $R(X)=\prod_j(X-z^j)^{w(j)}$. The largest integer $B$ for which **every** equality $R(z^x)=R(z^y)$ at two points outside the support lifts to the complex roots for all $|w(j)|\le B$ is **67 at the first prime and 62 at the second**. Both bounds have explicit failures at $B+1$ with disjoint numerator and denominator supports. The two monic locator degrees agree by the zero-sum condition.

| Named field | Sharp $B$ | Witness maximum weight | Witness degrees | Test exponents | Common value in the finite field |
|---|---:|---:|---:|---|---:|
| First | 67 | 68 | 1,789 | 0, 15 | 125724911936549340355751601727278584944565803988 |
| Second | 62 | 63 | 1,702 | 0, 1 | 420124664607191906627460135786136923077171842045 |

The certificate contains the two complete 64-entry integer vectors. Its verifier evaluates the quotients in the original fields and checks a nonzero primitive-unit exponent in both cases, which excludes equality in characteristic zero by independence. A different primitive-root choice reindexes the supports and test centers. [Witnesses and separating rows](../../../scripts/probes/mu64_balanced_weight_certificates.json) · [Complex independence](quarter-dyadic-parity.md#independence-of-the-dyadic-cyclotomic-factors)

## Retaining the phase of a balanced comparison

Put $\Delta=R(z^x)/R(z^y)$. Replacing $z$ by $z^{-1}$ in its expression gives $\Delta^*=z^{(y-x)\sum w}\Delta$ because the factor for each site $j$ acquires the multiplier $z^{y-x}$. Thus $\Delta^*=\Delta$ for a balanced signal. The identity is algebraic over the finite field itself, since $(X^{-1}-Z^{-1})/(Y^{-1}-Z^{-1})=(Y/X)(X-Z)/(Y-Z)$. [Lean inversion identity for multiset locators](../../../ArkLib/Research/ProximityGap/Frontier/DyadicUnitExponentBound.lean)

Write $u_r=1-z^r$, $r=1,3,\ldots,31$, and $\beta_r=(1-z^r)(1-z^{-r})$. The primitive-unit exponents $e$ of the ratio obey
$$
 \Delta\Delta^*=\prod_r \beta_r^{e_r}.
$$
Indeed $\Delta$ is a power of $z$ times $\prod u_r^{e_r}$, and inversion replaces every factor and the phase by their formal inverses of the site parameters. A finite equality consequently requires both $\prod\beta_r^{e_r}=1$ and $\prod u_r^{64e_r}=1$. The full discrete logarithms for the first condition follow from $\beta_r=-z^{-r}u_r^2$ and are checked against the original field. [Source full-group logarithms](mu128-unit-ellipsoid-transfer.md)

## Closed ellipsoids and integer separation

Translate one center to zero and let the other be $h$. All displacements are covered by $1\le h\le32$ by swapping the two centers and translating again. Delete the two center coordinates of $w$ and form the integral matrix $M$ of the comparison $e=Mw$. Its entries come from the primitive-unit factorization. The squared energy of $w$ is at most $62B^2$. In independent row coordinates this gives
$$
 e^\top(MM^\top)^{-1}e\le62B^2 .
$$
At shift 32 the last coordinate is recovered from the negative sum of the other fifteen. The verifier intersects the integral image lattice with the exact $\beta$-logarithm congruence, checks its lattice bases, and enumerates every point in the ellipsoid by rational arithmetic. [Projection and lattice construction](mu128-unit-ellipsoid-transfer.md)

For a nonzero candidate, a row $\lambda=(MM^\top)^{-1}e$ rules it out whenever $\lambda^\top e>B\|M^\top\lambda\|_1$. Further candidates are checked against the unsquared torsion condition. The remaining pairs $\pm e$ have small integer separating rows $(a,t)$ in the certificate. The checker verifies
$$
 a^\top e > B\|M^\top a+t\boldsymbol{1}\|_1 .
$$
This is impossible for $e=Mw$ with $\sum w=0$. It checks every supplied row is used. Only the zero exponent survives. For $e=0$, $\Delta$ is the same power of the primitive root in both characteristics, so the original equality lifts exactly.

The first field has 3,508 ellipsoid points across the 32 displacements and uses 47 final separating rows. The second field has 534 points and uses seven. The exact replay gives the same results with reversed starting bases. Run the verifier with `uv run --no-project --with python-flint python scripts/probes/probe_mu64_balanced_weight.py`, optionally adding `--reverse-basis`. [Verifier](../../../scripts/probes/probe_mu64_balanced_weight.py)

For an original simple equal-degree locator pair, taking products on whole cosets yields balanced signed populations on the quotient. The result therefore covers every order-64 quotient of a length-4,096 first-prime grid and every such quotient through length 2,048 at both primes. At second-prime length 4,096 the explicit weight-63 witness shows that quotient-product equality alone can fail to lift: realize each positive or negative population by selecting that many sites of its coset. Pointwise constancy of the original ratio throughout complete cosets imposes additional equations. [Coset product identity](dyadic-orbit-norm-split-pencils.md#norms-of-evaluations-on-complete-cosets)
