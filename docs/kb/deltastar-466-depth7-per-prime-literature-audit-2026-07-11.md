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

## 9. Ranked research consequences

1. **Exact dual coordinate, not a shortcut:** the annihilator-sensitive 13-variable Jacobi law
   is equivalent to the centered fourteenth moment after the principal-character shift. Attack
   its off-diagonal/Wick remainder only when the argument uses additional production-specific
   structure; generic Jacobi orthogonality alone has already been exhausted.
2. **Best exact formal bridge:** formalize `A=VDV`, singular values `m|eta_j|`, and the
   Schatten-14 equivalence. This does not close the lane but prevents determinant/geometric-mean
   arguments from being mistaken for moment bounds.
3. **Correct probabilistic formulation:** seek centered `L2` fixed-depth mixing at ambient scale
   `1/q`; generic inverse-LO `L-infinity` contraction at scale `1/n` is off by the entire density
   ratio.
4. **Do not reopen:** arbitrary-set Chang, small-gcd sparse polynomial estimates, exact additive
   irreducibility, determinant-only cyclotomic identities, or fourth-energy interpolation. Their
   production failures above are numerical or structural, not a matter of optimizing constants.

The current literature therefore supplies a sharper research object and two useful formal
no-go certificates, but no proof of the repaired depth-seven inequality.
