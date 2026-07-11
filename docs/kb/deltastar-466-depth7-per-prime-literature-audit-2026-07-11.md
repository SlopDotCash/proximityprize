# #466: depth-seven per-prime literature audit (2026-07-11)

## Scope and verdict

This note audits primary papers and preprints against the repaired production target

\[
  qE_7-n^{14}\le q\,2^{18}n^7,
  \qquad n=2^{30},
  \qquad q=n(2^{128}+192)+1.
\]

Here

\[
q=365375409332725729550921208179070755120141565953,
\quad 2^{158}<q<2^{159},
\]

so

\[
  \beta=\log_n q=5.266666\ldots<5.3,
  \qquad m=(q-1)/n=2^{128}+192.
\]

The target is equivalent to

\[
  \sum_{b\ne0}|\eta_b|^{14}\le q\,2^{18}n^7,
\]

and also to the centered sevenfold-mixing estimate

\[
  \sum_{x\in\mathbf F_q}
  \left(\frac{r_7(x)}{n^7}-\frac1q\right)^2
  \le \frac{2^{18}}{n^7}.
\]

No theorem found closes this inequality for the fixed production prime. A 13-variable Jacobi
correlation is an exact on-target coordinate system, but the post-audit orthogonality calculation
shows that its proposed `m^7` estimate is equivalent to the centered physical-space fourteenth
moment rather than an independent shortcut. Lu--Zheng's published theorem applies to it exactly,
but its numerical upper bound misses even a deliberately over-generous budget by strictly between
factors `2^701` and `2^702`.

The deterministic audit is
[`probe_bgk_depth7_perprime_literature_20260711.py`](../../scripts/probes/probe_bgk_depth7_perprime_literature_20260711.py),
with checked output in
[`_out_bgk_depth7_perprime_literature_20260711.txt`](../../scripts/probes/_out_bgk_depth7_perprime_literature_20260711.txt).
The two largest exact arithmetic exclusions are independently formalized in
`Frontier/_BGKJacobiTensorProductionGap.lean`: the squared `701--702` bit Jacobi gap, the
sparse-polynomial gcd failure `m^299>q^91`, and the production bracket `2^158<q<2^159` are all
axiom-clean Lean theorems.

An additional exact quotient-order factorization, now checked in the same file, is

```text
m = 2^6 * 7^3 * 26407 * 279991 * 4533259 * 462478642316479903.
```

This makes a CRT decomposition of the annihilator character group testable.  It does not by
itself factor Jacobi phases, so no analytic saving is inferred from the arithmetic factorization.

## 1. Exact Jacobi-sum reduction: socket and post-audit equivalence

Let `K` be the subgroup of multiplicative characters of `F_q^*` trivial on `G=mu_n`.
Then `|K|=m`; write `K*=K\{1}` and normalize nontrivial Gauss sums by
`g(chi)=q^(-1/2)G(chi)`. The all-nontrivial part of the fourteenth-moment expansion contains

\[
S_{13}(K)=
\sum_{\substack{(\alpha_1,\ldots,\alpha_{13})\in(K^*)^{13}\\
                  \alpha_1\cdots\alpha_{13}\ne1}}
q^{-6}J(\alpha_1,\ldots,\alpha_{13}).
\]

This identity is exact, not a heuristic. Start with seven `chi` and seven `rho` characters under
`prod chi_i=prod rho_j`, eliminate `rho_7`, and put

\[
(\alpha_1,\ldots,\alpha_{13})
=(\chi_1,\ldots,\chi_7,\rho_1^{-1},\ldots,\rho_6^{-1}).
\]

Their product is `rho_7`, which is nontrivial on this stratum. Since `-1 in G`, every character
in `K` takes value one at `-1`; hence

\[
q^{-7}\prod_{i=1}^7G(\chi_i)\prod_{j=1}^7G(\rho_j^{-1})
=q^{-6}J(\alpha_1,\ldots,\alpha_{13}).
\]

The top-stratum contribution is

\[
  \frac{(q-1)q^7}{m^{14}}S_{13}(K).
\]

Even if this one stratum is given the entire coefficient `2^18`, its exact socket is smaller than

\[
  2^{18}m^7;
\]

the exact factor is `2^18 m^7 ((q-1)/q)^6`.

[Lu and Zheng, *On the distribution of multivariate Jacobi sums*, Theorem 4, equation (4)](https://arxiv.org/abs/2005.14358)
prove, for arbitrary nonempty character sets `A1,A2,B`,

\[
|M^{(h)}|\le h\sqrt{A_1A_2q}\,B.
\]

Taking Jacobi arity 13, moment index `h=1`, `A1=A2=K*`, and `B=(K*)^11` gives the exact
applicable bound

\[
  |S_{13}(K)|\le (m-1)^{12}\sqrt q.
\]

At the production values,

\[
2^{701}\,(2^{18}m^7)
<(m-1)^{12}\sqrt q
<2^{702}\,(2^{18}m^7).
\]

Thus this theorem cancels two character variables and pays cardinality for the other eleven.
Its discrepancy theorem, `D <= C(q/(A1 A2))^(1/4)`, does not improve the first-moment bound
after multiplication by the `m^13` family size.

### Full orthogonality identifies the same centered wall

Let `c` run over `F_q^*/G`, and let `eta_c` be the corresponding Gauss period. Deleting the
principal character gives

\[
  A_c=\frac{m\eta_c+1}{\sqrt q}.
\]

Complete character orthogonality, rather than a triangle bound on the thirteen free variables,
then proves the exact identity

\[
  S_{13}(K)
  =\frac1m\sum_c A_c^{14}
  =\frac{m^{13}}{q^7}\sum_c\left(\eta_c+\frac1m\right)^{14}
  =(a^{*14})(1)=\lVert a^{*7}\rVert_2^2\ge0,
\]

where `a(1)=0` and `a(chi)=g(chi)` on `K*`. Consequently

\[
 S_{13}(K)\le C m^7\left(\frac{q-1}{q}\right)^6
 \quad\Longleftrightarrow\quad
 \sum_c\left(\eta_c+\frac1m\right)^{14}\le C q n^6.
\]

Thus the proposed tensorization law is not noncircular: after all available orthogonality it is
the centered depth-seven moment in dual coordinates. The only remaining distinction is the
principal-character shift `1/m` and its boundary allocation. The formal normalization,
positivity, equivalence, and an aligned-phase no-go witness are in
`Frontier/_AJT13CenteredMomentEquivalence.lean`.

The boundary allocation is now exact at Wick scale.  Weighted convexity gives

\[
 (x-c)^{14}\le(21/20)^{13}x^{14}+21^{13}c^{14}.
\]

Summing with `c=1/m`, the translation error is at most `21^13/m^13<=1` for `m>=21`, while
`135135(21/20)^13+1<2^18`.  Hence a centered coefficient-`13!!` theorem implies the original
uncentered coefficient-`2^18` target.  This is formalized in
`Frontier/_AJT13CenteredBoundaryBridge.lean`; lower principal-character strata are therefore not
a separate obstruction once Wick-scale centered control is available.

The inverse-pair diagonals have Wick coefficient `13!!=135135`, leaving `127009` beneath the
public coefficient `2^18`. The genuine analytic question is therefore to control the
off-diagonal correlation or to exploit the production thinness. Small exact cells also show
that `2^18` is not a universal constant across arbitrary subgroup regimes: at
`(n,m,q)=(256,52,13313)`, `S13/m^7=313471.7745...>2^18`. CRT splits the character labels but
not the additive Gauss phases; already at `(q,n,m)=(13,2,6)` a punctured CRT minor has magnitude
`sqrt(48/13)`, ruling out rank-one tensor factorization.

### Two structural theorem templates also fail before production arithmetic enters

The exact centered-translate identity suggests bounding a zero-mean, additive-positive-definite,
multiplicatively invariant kernel on `1-G`.  `_BGKCenteredTranslatePDNoGo.lean` proves those three
properties alone are insufficient: a centered-delta kernel on `ZMod 5` has an unbounded positive
scaling ray.  The actual centered autocorrelation in the exact proper-subgroup cell
`(p,n)=(13313,256)` has normalized depth-seven coefficient

```text
584598921140164042747377 / 1873638182474481664
  = 312012.706... > 2^18.
```

This is not a counterexample in the production regime.  It rules out a universal restriction or
hypercontractive theorem whose only hypotheses are those homogeneous structural properties.
In Fourier coordinates the boundary is exact: `_BGKCenteredTranslateConeDuality.lean` proves the
unit-mass nonnegative orbit-spectral cone has optimum
`max_(b!=0)|eta_b|^2/|G|`, attained on a single orbit.  Thus this cone relaxation is precisely
the worst-period problem.  The actual weights `|eta_b|^12` are a genuine extra constraint, but
`_BGKLowerMomentOrbitSpikeNoGo.lean` shows scalar information does not capture it: an explicit
production-scale orbit profile satisfies exact Parseval mass, the trivial cap, and even
hypothetical Wick ceilings through power six while its seventh power sum is between `2^15` and
`2^16` times the target.  A useful theorem must couple the full period profile at seventh order.

Likewise, the exact marked-sunflower decomposition does not license termwise positive bounds.
After `D_0=D_1=0`, even the optimistic completed Wick coefficient at depth two is
`158760>126871`; depths `2,...,6` total `2714355`, between 21 and 22 copies of the entire injective
allowance.  `_BGKSevenOverlapProductionBudget.lean` kernel-checks these constants and maps marked
depth-two pairs into the projective-accident classifier.  The viable literature target is
therefore a centered joint-cancellation or production-arithmetic theorem, not an improvement of
independent positive collision counts.

The corresponding signed inversion is now audited as well.  The Catalan--Lagrange inverse writes
`D_7` as an alternating combination of `W_2,...,W_7`, but
`_BGKMarkedSunflowerInverse.lean` proves it is equivalent to the forward seventh row once the
lower rows are fixed.  Its production coefficient mass lies between `2^143` and `2^144`; this is
amplification rather than an automatic loss because depth-normalized bounds can compensate.
Consequently the inverse is a useful coordinate only if a theorem couples adjacent depths or
supplies the correct cyclotomic scaling.  At depth two, the exact conditional socket is now
`kappa_(2^30)` difference-signature injectivity modulo inversion; no production proof of that
condition is currently present.
The generic correlated-sunflower alternative is now closed too.  The exact adjacent inequalities
from total positivity point in the lower-growth direction, and the pure ray `D_7=T` has all lower
rows zero while its generating polynomial `T z^7(1+z)^(n-14)` is already real-rooted/PF-infinity.
Its Wick coefficient is `135135=126871+8264`, so even perfect removal of all proper depths leaves
a `6.115...%` primitive arithmetic saving.  `_BGKSunflowerCorrelationNoGo.lean` also provides the
surviving coefficientwise/additive-character transform and a modulo-29 label coordinate.
`_ANT46KappaProductionReduction.lean` makes the size of that condition explicit.  A transversal
discriminant certificate has degree `536870911` and Sylvester order `1073741821`, so literal
resultant expansion is billion-scale.  Projecting away small cofactor components leaves
prime-order separation problems of 59 and 67 bits for the two production primes.  The existing
order certificates prove these target group shapes but not injectivity of the projected
cyclotomic-unit values.
`_ANT46ProjectedCharacterNoGo.lean` tests the natural character and cyclotomic-number follow-up.
It proves exact Jacobi-mode, cyclotomic-intersection, and cyclotomic-unit/Kummer forms, but
modewise Weil estimates miss the collision-injectivity floor by 127--129 bits.  The hypothesis in
[Do Duc--Leung--Schmidt](https://arxiv.org/abs/1903.07314) would require
`P>(sqrt(14))^k`; both production primes instead satisfy `P^2<14^k`.  The paper therefore does not
certify the projected separation.

There is now an exact finite certificate format.  `_ANT46ProjectedKappaBucketCertificate.lean` proves that
per-bucket value `Nodup` plus cross-bucket disjointness certifies the projected map, with a keyed
variant in which disjointness is automatic.  Its natural modular evaluators are formally bridged
to both production maps.  The certificate necessarily evaluates all `2^29=536870912`
inversion-class representatives; a raw 20-byte table is 10 GiB, and `2^20` buckets only reduce the
working set to 512 entries per bucket.  Thus this is plausible finite verification, not analytic
compression or a proof already in hand.  The recent general hardness result of
[Qiu--Cao--Huang--Feng--Gao](https://arxiv.org/abs/2606.12144) for roots-of-unity detection of
sparse finite-field polynomials further cautions against expecting a generic output-sensitive
shortcut; it does not preclude a production-specific certificate.

### The published subset-sum asymptotic is vacuous in the thin-subgroup cell

The exterior-power reformulation makes one older theorem look almost tailor-made.  If
`a_y` counts seven-subsets of `G` with sum `y`, then the remaining injective target is exactly

\[
  (7!)^2\sum_y(qa_y-\binom n7)^2\le 126871q^2n^7.
\]

[Zhu and Wan, *An asymptotic formula for counting subset sums over subgroups of finite fields*,
Theorem 1.1](https://arxiv.org/abs/1101.0289) prove, for a subgroup of index `m` and nonzero `y`,

\[
 \left|a_y-q^{-1}\binom n7\right|
 \le {2\sqrt q\over q}
   \binom{\sqrt q+7+q/(mp)}7,
\]

where `p` is the field characteristic.  In the production prime field `p=q`, so `q/(mp)=1/m`,
but the subgroup index is `m=2^128+192` while `sqrt(q)` is between `2^79` and `2^80`.
Consequently the paper's later useful range `m<c sqrt(q)` is missed by more than 48 bits.
More decisively, the displayed error term is at least

\[
 {2\over\sqrt q}{(\sqrt q)^7\over7!}
 ={2q^3\over7!}>2^{462},
\]

whereas the entire seven-subset fibre population is
`C(2^30,7)<2^210`.  Thus this theorem is not merely short of the centered variance constant: in
the production thin-subgroup regime its per-fibre error exceeds the trivial total-population
bound by over 252 bits.  The Li--Wan distinct-coordinate sieve supplies the exact combinatorial
language used by the new injective bridge, but its termwise Weil estimate cannot prove the needed
joint L2 cancellation.  The squared index comparison and the `462`/`252`-bit production gaps are
kernel-checked in `Frontier/_BGKSubsetSumLiteratureProductionGap.lean`.

## 2. Fixed-depth inverse Littlewood--Offord does not center

[Costa, *Anticoncentration of Random Sums in Z_p*, Theorems 3.3 and 3.5](https://arxiv.org/abs/2602.16595)
is a directly relevant February 2026 result. For three iid variables whose atoms are at most
`lambda <= 9/10`, with `p>2/lambda`, it proves

\[
  \max_x \Pr(Y_1+Y_2+Y_3=x)\le C_3\lambda,
\]

for an absolute `C3<1`; the proof reports an explicit contraction
`C3 < 1-2.27*10^(-12)`. An earlier footnote in the preprint prints `1.3*10^(-12)` instead;
the probe uses the stronger concluding computation. Either printed value gives the same bit
brackets below. Convolution with the remaining four variables preserves the bound, so for
uniform `X` on `G` and `ell=7`,

\[
  r_7(x)/n^7\le C_3/n,
  \qquad E_7\le C_3n^{13}.
\]

The condition `q>2n` is amply satisfied. The problem is scale, not applicability. This yields

\[
qE_7-n^{14}\le qC_3n^{13}-n^{14}.
\]

Using the paper's explicit loose constant, this upper bound lies strictly between `2^161` and
`2^162` times the desired centered target. For an `E7 <= C3 n^13` theorem to close, it would need

\[
  C_3\le n/q+2^{18}/n^6,
\]

and the right side is between `2^(-129)` and `2^(-127)`. Generic fixed-depth
anti-concentration lives at the support scale `1/n`; the target asks for centered `L2` mixing at
the ambient scale `1/q`.

This is a decisive inverse-LO no-go and also identifies the missing theory: a **centered L2
anti-resonance theorem**, not another `L-infinity` concentration inequality.

## 3. The strengthened Chang lemma is cardinality-vacuous here

[Carenini and Franchi, *A Strengthening of Chang's Lemma*, Theorems 4.1 and 4.2](https://arxiv.org/abs/2605.07916)
extends the May 2026 result to arbitrary finite abelian groups. It places `Spec_epsilon(A)` inside
the `{-1,0,1}`-span of a dissociated set of size

\[
  r\le 2\epsilon^{-2}\log(1/alpha).
\]

For `A=G` in the additive group of `F_q`, `alpha=n/q`. Even in the limit `epsilon -> 1`,

\[
  2\log(q/n)=177.445678\ldots,
  \qquad \log_3 q=99.686901\ldots.
\]

Therefore the only automatic span-cardinality estimate, `|<Lambda>| <= 3^r`, already exceeds
the whole dual group for every admissible epsilon. The paper also says explicitly that its
finite-abelian formulation does not currently admit the localized additive-counting analogue of
its finite-vector-space Proposition 1.5. Thus neither Theorem 4.1 nor the refined weights in
Theorem 4.2 give a production high-spectrum tail bound beyond Parseval.

The Lean-able no-go is the numerical inequality

```text
log 3 * (2 * log (q / n)) > log q.
```

## 4. A new cyclotomic matrix gives an exact Schatten bridge, not a bound

[Wu and Wang, *The Gauss periods and cyclotomic matrices involving Gauss sums over cyclic groups*,
Theorem 1.1 and equation (2.4)](https://arxiv.org/abs/2607.02392) is a July 2026 preprint.
For `N=p^a`, `phi(N)=kd`, it factors its `d`-by-`d` cyclotomic matrix as

\[
  A_k(\chi)=VDV,
\]

where `V/sqrt(d)` is unitary and `D` is diagonal with the `d` conjugate Gauss periods.
For the production prime take the paper's `k=n` and `d=m`. Unitary invariance of singular
values then gives the new exact bridge

\[
  s_j(A_n)=m|\eta_j|,
  \qquad
  \|A_n\|_{S_{14}}^{14}=m^{14}\sum_{j=0}^{m-1}|\eta_j|^{14}.
\]

Since each period occurs at `n` nonzero additive frequencies, the repaired target is equivalent to

\[
  \|A_n\|_{S_{14}}^{14}
  \le m^{14}q\,2^{18}n^6.
\]

This identity is worth formalizing: it makes the exact matrix norm consumer explicit. But the
paper's theorem controls `det(A_n)`, hence the product/geometric mean of the singular values.
It supplies no Schatten-14 upper bound. Constant-modulus matrices can be rank one, so entrywise
Gauss magnitude and determinant data cannot supply the missing upper moment.

[Wu and Ji, *Products involving the real parts of Jacobi sums and related cyclotomic matrices*](https://arxiv.org/abs/2605.27169)
similarly obtains determinant/product identities, but only for a special quadratic-character
matrix of dimension `(q-1)/2`. It neither matches the order-`2^30` subgroup nor gives an upper
Schatten moment.

The different 2026 determinant of [Wu, Wang, and Pan, *On p-th cyclotomic field and cyclotomic
matrices involving Jacobi sums*](https://arxiv.org/abs/2506.14316) equals a signed power of the
index times the linear coefficient of the Gaussian-period minimal polynomial.  This is a genuine
new exact coordinate, but one cofactor symmetric function does not control the house.
`_BGKPeriodProfileArithmeticAudit.lean` makes that failure formal: the irreducible monic family

```text
X^4 + X^3 + (1-A(A+1))X^2 + X + 1
```

has fixed norm, trace coefficient, and linear coefficient, yet has a real root in `[A/2,A]`.
The same audit shows where actual period arithmetic begins to matter: Galois transitivity and a
necessary moment congruence each kill the literal rational orbit spike.  Nevertheless a nonzero
integral, trace-correct profile still passes the Wick ceilings through depth six and fails depth
seven by 8--9 bits.  The missing theorem must quantitatively couple all totally-real ramified
conjugates; determinant, integrality, and isolated residues do not suffice separately.

## 5. Sparse-polynomial estimates fail the production gcd gate

[Bhakta and Shparlinski, *Exponential Sums with Sparse Polynomials and Distribution of the Power
Generator*](https://arxiv.org/abs/2412.07989) records the monomial estimate

\[
  |S_q(aX^d)|\ll d^{1/2}q^{2/3}(\log q)^{1/6}.
\]

For `d=m`, `S_q(aX^m)=1+m eta_a`, so it yields

\[
  |\eta_a|\ll \sqrt n\,q^{1/6}(\log q)^{1/6}.
\]

Before the logarithm and implied constant this is already between `2^(68/6)` and `2^(69/6)`
times worse than the trivial `|eta_a|<=n`.

Their genuinely sparse Theorem 2.1 requires, at its most permissive `epsilon=3/92`,

\[
  \gcd(e_i,q-1)\le \tfrac12q^{91/299}.
\]

The production monomial exponent satisfies `gcd(m,q-1)=m`, and the exact integer certificate

\[
  m^{299}>q^{91}
\]

shows failure before any analytic estimate is invoked. Sparse-polynomial technology designed for
small exponent gcds excludes precisely the subgroup quotient exponent.

There is now an exact sparse-polynomial formulation of the primitive packet itself.
`_BGKPrimitiveDepthSevenSparseCodeNoGo.lean` proves that every production primitive witness gives
a nonzero integer polynomial of degree `<2^29`, support and `l1` mass at most `14`, coefficient
height at most `14`, and a certified production root.  `_BGKPrimitiveFoldedAlphabet.lean` sharpens
the actual-witness height to `2`, proves the coefficient alphabet `{-2,-1,0,1,2}`, and classifies
the exact nine local source profiles.  At each production root it retains a nonzero resultant
divisible by `P` with absolute value at most `14^(2^29)`; the norm base does not improve because
the `l1` mass remains `14`.  The five-letter class is not universally kernel-free: an exact
order-`16` collision at `g=3` in `ZMod 17` has globally disjoint petals and folded vector
`[1,2,1,2,2,2,2,0]`, proving coefficient height `2` sharp.  Hence the surviving input must be
production-specific arithmetic or an average count, not alphabet alone.  The ambient
field-coefficient relaxation remains a one-check code of exact distance two, support-isometric for
every nonzero root, so ordinary coding parameters are blind to the arithmetic.

The source fibers now have an exact local law and a formal global enumerator.  Their weights are
`xy`, `x+y`, and
`1+x^2+y^2` for letters of absolute value two, one, and zero.  The resulting occupancy law makes
the unit-letter count even and shows the only 14-coordinate sector is the all-`+-1` sector, with
formal fixed-label ordered factor `14!`; every nonunit sector uses at most 13 coordinates.  Its
smaller ambient source mass cannot be transferred to the collision event without the same missing
equidistribution input, so this refines rather than closes the production-specific count; the full
cardinality equivalence is not yet packaged in Lean.

[Kelley, *Roots of Sparse Polynomials over a Finite Field*](https://arxiv.org/abs/1602.00208)
bounds roots of a `t`-nomial by
`2(q-1)^(1-1/(t-1)) C^(1/(t-1))`.  Even granting the best possible `C=1`, the `t=14` scale is
`2^146--2^148` for the first prime and `2^147--2^149` for the second, over 116 bits above the
entire order-`2^30` subgroup.  A useful sparse theorem must exploit the tiny signed integer
alphabet/constant-weight slice, not only support size.

## 6. Current fourth-energy input is 145 bits short

[Cheong, Ge, Koh, Pham, Tran, and Zhang, *Additive structures imply more distances in F_q^d*,
Lemma 26](https://arxiv.org/abs/2510.26364) uses Shkredov's primary fourth-energy theorem

\[
  E_2(G)\ll n^{22/9}\log n
  \qquad(n\le q^{3/5}).
\]

The production parameters satisfy the size hypothesis. Combining it only with
`|eta_b|<=n` gives

\[
\sum_{b\ne0}|\eta_b|^{14}
\le n^{10}\sum_b|\eta_b|^4
\ll qn^{112/9}\log n.
\]

Relative to `q 2^18 n^7`, the factor before the implied constant and logarithm is

\[
  n^{49/9}/2^{18}=2^{145+1/3}.
\]

Thus a current `E2`-only Salem/restriction input cannot reach a centered depth-seven moment.

For comparison, [Shkredov, *Some remarks on the asymmetric sum-product phenomenon*, Corollary
16](https://arxiv.org/abs/1705.09703) gives, for `n>=q^delta`,

\[
  \max_{b\ne0}|\eta_b|
  \ll n q^{-\delta/2^{7+2/\delta}}.
\]

Here `delta=log_q n=0.189873...`; the saving is only
`n^(-0.0000052715...)`, or `0.0001582` bits at `n=2^30`, before the ineffective fixed-prime
constant. This baseline was already known in the campaign and is not a new route.

## 7. Exact additive irreducibility is the wrong stability level

[Kalmynin, *On additive irreducibility of multiplicative subgroups*](https://arxiv.org/abs/2504.10202)
proves strong exact statements: `A-A=mu_d union {0}` only for `d=2,6`; a nontrivial exact
decomposition `mu_d=A+B` forces `|A|=|B|=sqrt(d)`; and a proper subgroup is not an exact
threefold sumset.

These theorems do not control `E7`. Failure of the centered moment can feed a
Balog--Szemeredi--Gowers argument only to structured subsets or approximate sumsets, not to an
exact decomposition of the whole subgroup. No quantitative stability statement in the paper
turns an `L2` representation excess into one of its forbidden equalities. The type mismatch is
therefore decisive, despite the strength of the exact irreducibility results.

## 8. Current generalized-Paley classification has no magnitude estimate

[Podesta and Videla, *The nature of the spectrum of generalized Paley graphs and weak Waring
numbers over finite fields*](https://arxiv.org/abs/2604.06513) classifies reality and several
integrality/three-eigenvalue cases. Because `-1 in G`, the production graph is undirected and its
spectrum is real, but the paper gives no generic nonprincipal eigenvalue magnitude bound for this
thin, growing-index family. Its explicit families are special integral, semiprimitive, or Hamming
regimes, not the production prime.

The recent regular-graph trace identities of [Bašić, Smajlović, and
Šabanac](https://arxiv.org/abs/2606.27075) make the Hashimoto polynomial explicit, but do not
perform Wick/injective subtraction.  `_BGKHashimotoWickSeparationNoGo.lean` computes the exact
degree-fourteen comparison: Hashimoto removes the 14 cyclically adjacent reversals, while the
first Wick pairing can occupy any of `C(14,2)=91` pairs, leaving `77d+14`.  An explicit closed
cyclically nonbacktracking word with repeated directions survives.  More fundamentally, two
unit-phase families have the same first power sum (ordinary adjacency eigenvalue) and opposite
ordered-injective transforms, so no univariate adjacency polynomial can recover the packet.
[Bal's irregular edge-space invariants](https://arxiv.org/abs/2604.20578) explicitly collapse to
adjacency-side data in the regular case.  A graph-theoretic survivor must therefore be a
dilation-coloured operator theory retaining `b,2b,...,7b`, followed by the same primitive
sunflower arithmetic; ordinary Ihara--Bass is not an independent source of the 6.115% saving.

That coloured object is now exact.  `_BGKDilationColoredNewtonOperatorNoGo.lean` proves the seven
dilated convolution operators commute, diagonalize on additive characters with eigenvalues
`eta_b,...,eta_(7b)`, and recover the ordered-injective transform through the full Newton
polynomial.  It also proves why individual operator bounds cannot finish the argument: dilation
permutes frequencies, so every colour has the same complete marginal Schatten profile.  Two
commuting real diagonal joint spectra with identical marginal profiles lie on opposite sides of
the production allowance, with energies `66816<126871<25401600`, and the Newton scalar has both
signs on commuting contractions.  The graph survivor is therefore a genuinely mixed arithmetic
joint-spectral inequality, not another one-colour trace estimate or generic SOS argument.

The same obstruction survives a common dilation action.  In
`_BGKDilationPermutationCopulaNoGo.lean`, two equimeasurable sign profiles on `ZMod 13` generate
all colours by `f(jb)`, so every colour really is the same base spectrum pulled back by a
multiplier permutation.  All marginal moments agree, but the normalized Newton energies satisfy
`953600<13*126871<64641152`.  The profiles are not asserted to be actual periods; the result says
the missing theorem must use the Fourier-of-subgroup realization, not dilation compatibility
alone.

The actual subgroup joint law is now exact at second order and reduced to collisions at every
higher order.  `_BGKActualJointPeriodLaw.lean` proves a general weighted mixed-moment identity and
certifies that colours `1,...,7` occupy distinct cyclotomic classes at both production primes.
Their nonzero-frequency Gram matrix is therefore a regular simplex with diagonal `q*n-n^2` and
off diagonal `-n^2`.  This excludes the aligned abstract copula, but the pair correlation is
123--124 bits below the required leakage.  The first deleted-pair transition is
`q*(A+n-2M)`; under a `2^22` nonzero-shift representation cap, antipodal energy makes a
`3 -> 2` defect require `M>2^59` while the cap gives `M<=2^52`.  Pairwise information therefore
does not supply the later signed higher-collision correlation that remains open.

All convolution-power Schur/Krein nonnegativity and orbit-invariance constraints in the enlarged
spectral cone are also insufficient.  In the translation scheme, entrywise multiplication of
kernels is additive convolution of their Fourier profiles.
`_BGKCyclotomicKreinSchurNoGo.lean` proves that nonnegative multiplicative-orbit profiles remain
admissible under every convolution power, so the single-orbit extremizer survives all Schur powers
and the cone optimum is still exactly the worst period square.  The generic valency relaxation
misses by 191--192 bits.  [Nomura and Terwilliger](https://arxiv.org/abs/2405.10491) identify the
intersection/Krein equality in the formally self-dual setting; the surviving cyclotomic-scheme
route must use the actual arithmetic intersection numbers and their nonlinear coupling, not only
Krein nonnegativity.

The first exact-integrality follow-up is also now bounded.  For the literal translation-relation
intersection count `p_ST(z)=#{x in S:z-x in T}`,
`_BGKCyclotomicIntersectionIntegralityAudit.lean` proves that its character transform is the
product of the relation periods, together with its exact row mass and multiplier-orbit
invariance.  Cauchy--Davenport excludes concentration on one cyclotomic class at either production
prime, but the resulting integral relaxation admits `(2^30-1,1)`.  It forces one leaked unit; the
primitive ratio requires exactly `65,663,244`, between `2^25` and `2^26`.  Hence a useful
cyclotomic-matrix identity must constrain the correlated values or placement of many entries;
integrality, row sums, and two-cell support alone miss by 25--26 bits.

## 9. Standard seven-step flattening inputs miss the exact entropy budget

`_BGKSevenStepFlatteningProductionNoGo.lean` rewrites the injective target as an exact collision-
entropy statement.  The permitted normalized chi-square divergence is between `2^-36` and
`2^-35`.  A six-transition proof with uniform normalized integer contraction numerator `c` needs

```text
c^6 <= 126871;   7^6 = 117649 < 126871 < 262144 = 8^6.
```

Thus each convolution needs more than 27 `L2` bits of contraction.  The positive BSG scale loses
98--99 bits before extracting one point.  Even granting the shifted-subgroup cap
`4*n^(2/3)=2^22` from the Shkredov--Vyugin intersection theory saves only eight bits, leaving an
exact 19-bit one-step gap.  [Hart's sixfold-covering theorem](https://arxiv.org/abs/1303.2729)
requires a density inequality whose production specialization is reversed by over 1048 bits, and
support covering alone does not upper-bound collision entropy.  The viable invention is a
centered trajectory-weighted flattening theorem, not ordinary raw-energy BSG or sumset growth.

`_BGKWickTrajectoryDefectBudget.lean` pins the smallest useful improvement.  The Wick transition
numerators `3,5,7,9,11,13` multiply to `135135`, whereas the exact production trajectory allowance
is strictly between `126871` and `126872`.  Decreasing any one numerator by one makes the product
at most `124740<126871`; multiplying all six improved-profile bounds by `501/500` still fits.
Its abstract six-ratio telescopes prove the final depth-seven target from either the exact or this
robust profile.  Thus a single one-unit Wick
defect at any transition is sufficient while the other five remain at Wick scale; proving that
defect for the actual subgroup trajectory is still open.

The actual trajectory rules out one of those six locations.  `_BGKCenteredTrajectoryContraction`
proves the exact six-step variance consumer and the full deleted-diagonal Newton transition, then
uses the forced antipodal zero-sum fiber to show

```text
n*Z_2/Z_1 > 3 + 2^-29.
```

Consequently the first transition obeys neither Wick `3` nor the robust selected cap
`2*(501/500)`; the defect must occur among the five later steps.  An order-eight subgroup in
`ZMod 17` also forces a universal product at least `8^6`, so no field-uniform version can close
the production target.  The forced first-step lower proxy lies within the ordinary `3.006` robust
allowance, but no matching upper bound is claimed.

## 10. Ranked research consequences

1. **Exact dual coordinate, not a shortcut:** the annihilator-sensitive 13-variable Jacobi law
   is equivalent to the centered fourteenth moment after the principal-character shift. Attack
   its off-diagonal/Wick remainder only when the argument uses additional production-specific
   structure; generic Jacobi orthogonality alone has already been exhausted.
2. **Best exact arithmetic target:** couple the full ramified Galois orbit or the simultaneous
   period-power residues strongly enough to exclude the remaining integral spike. One Jacobi
   determinant, one congruence, norm, trace, and irreducibility are now formally insufficient.
3. **Correct probabilistic formulation:** seek centered, trajectory-weighted `L2` fixed-depth
   mixing at ambient scale `1/q`.  The first transition is excluded; it suffices to lower one of
   the five later Wick numerators by one while keeping every step inside the `501/500` robust
   envelope. Standard positive BSG, one-shift intersections, and support covering are
   quantitatively excluded.
4. **Correct sparse formulation:** count the five-letter, support-14, `l1<=14` integer kernel slice
   at the two explicit roots.  Its nine local profiles are formal, but the sharp `ZMod 17`
   collision rules out universal alphabet-only kernel-freeness; ambient coding invariants and
   generic fewnomial root counts are quantitatively blind.
5. **Do not reopen:** arbitrary-set Chang, small-gcd sparse polynomial estimates, exact additive
   irreducibility, determinant-only cyclotomic identities, or fourth-energy interpolation. Their
   production failures above are numerical or structural, not a matter of optimizing constants.

The current literature therefore supplies a sharper research object and several useful formal
no-go certificates, but no proof of the repaired depth-seven inequality.
