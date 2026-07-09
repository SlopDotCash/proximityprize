# Multi-coordinate information sets: valid reduction, unchanged global wall (2026-07-09)

## Question

Suppose a family of RS witness columns has a decomposition

\[
  X_j=a+\gamma_j b+\sum_{\ell=1}^{d}(w_j)_\ell c_\ell,
\]

where the `c_ℓ` span a `d`-dimensional subspace `W` of degree-`<k` RS codewords.  Every
witness set `Z_j` has cardinality `a=k+m`.  Can many coordinates be used at once to force a
large subfamily of the columns into one affine codeword pencil, and hence invoke
`_DesignMatrixAffineCluster.lean`?

The local reduction is valid.  Its worst-case global output is

\[
  |G|\binom{m+d}{d}\le (n-d)\binom nd,
  \qquad
  |G|\le (n-d)\frac{\binom nd}{\binom{m+d}{d}}.                 \tag{1}
\]

Thus it lands exactly on the known information-set ratio wall (with the harmless improvement
`n -> n-d` in the affine-cluster factor).  It does not prove the prize good side.

## 1. Polynomial-subspace information-set count

Let `I ⊆ Z` be an information set of size `i<d`: the evaluation rows on `I` are linearly
independent.  Put

\[
  K_I=\{p\in W:p|_I=0\}.
\]

Then `dim K_I=d-i`.  A coordinate `x` fails to extend `I` precisely when every polynomial in
`K_I` vanishes at `x`.  The RS generalized-MDS zero bound says that an `r`-dimensional nonzero
subspace of degree-`<k` polynomials has at most `k-r` common zeros.  Therefore the number of
non-extensions is at most

\[
  k-(d-i)=k-d+i.
\]

Inside `|Z|=k+m`, every information `i`-set consequently has at least

\[
  (k+m)-(k-d+i)=m+d-i
\]

rank-raising extensions.  If `B_i` is the number of information `i`-sets, double-counting
marked extensions gives

\[
  (m+d-i)B_i\le(i+1)B_{i+1},\qquad B_0=1.
\]

Multiplication from `i=0` through `d-1` yields

\[
  B_d\ge\prod_{i=0}^{d-1}\frac{m+d-i}{i+1}=\binom{m+d}{d}.      \tag{2}
\]

The proposed count is therefore true; no counterexample exists under the stated degree and
dimension hypotheses.  The proof also shows exactly where the `degree < k` convention matters.

The axiom-clean Lean file
`Frontier/_MultiCoordinateInformationSetCount.lean` formalizes:

* the generalized-MDS common-zero inequality `|S|+finrank(W)≤k`;
* the exact marked-extension layer recurrence;
* recurrence (2) for an arbitrary independence predicate;
* the injective affine-preimage lemma used in the next step.

## 2. Shared information set implies simultaneous rank two

Fix an information `d`-set `I` contained in several witness sets `Z_j`, and let

\[
  \Phi_I:F^d\longrightarrow F^I,
  \qquad z\longmapsto\left(\sum_\ell z_\ell c_\ell(x)\right)_{x\in I}.
\]

By definition of information set, `Φ_I` is injective.  Agreement on `I` gives

\[
  \Phi_I(w_j)=(u_0-a)|_I+\gamma_j (u_1-b)|_I.
\]

If the fibre contains two distinct scalars, injectivity lifts this affine dependence:

\[
  w_j=v_0+\gamma_jv_1\quad\text{for every column in the fibre}.
\]

Hence all full columns in the fibre have the form `c_0+γ_j c_1`.  They are one affine
codeword cluster, not merely a low-rank surrogate.  This is the exact simultaneous rank-to-two
reduction sought in the sketch.

Moreover, the two anchor scalars show that the shared set `I` lies in the `lockedSet` of the
derived pencil: on `I`, both `c_0=u_0` and `c_1=u_1`.  Therefore the sharper theorem
`DesignMatrixAffineCluster.affineCluster_card_mul_le_support` gives

\[
  \max(1,a-|D|)|G_I|\le |\operatorname{supp}(u_1-c_1)|
     \le n-|D|\le n-d.
\]

In particular every information-set fibre has size at most `n-d` (a singleton fibre also
satisfies this whenever `d<n`).

## 3. Global double count and why it does not close delta-star

Count incidences `(j,I)` with `I⊆Z_j` an information `d`-set.  By (2), each column contributes
at least `C(m+d,d)` incidences.  There are only `C(n,d)` possible coordinate sets, and each fibre
has at most `n-d` columns.  This proves (1).

The loss is the ratio

\[
 R_d=\frac{\binom nd}{\binom{m+d}{d}}
    =\prod_{s=0}^{d-1}\frac{n-s}{m+d-s}\ge1
 \quad(m+d\le n).
\]

At the prize interior, `m/n=Θ(1/log n)`.  For fixed `d`,
`R_d=Θ((log n)^d)`.  Since `q≈n·2^128`, (1) only yields

\[
  |G|/q\lesssim 2^{-128}R_d,
\]

where the prize requires removal of the entire factor `R_d`.  Even `d=1` loses about `n/m`,
and the factor grows rapidly with `d`.  The improvement `n -> n-d` is negligible here.

This is not an algebraic failure: both the information-set count and the rank-to-two lifting are
correct.  It is a globalization failure.  To beat the wall one needs overlap/energy information
across different information sets, or a structural reason that the occupied `I`-fibres have much
smaller affine clusters than the worst-case `n-d`; independent per-fibre counting cannot do it.

## 4. Adversarial audit

* The common-zero estimate is sharp for polynomial spaces with a prescribed common factor of
  degree `k-d`.
* The marked-extension recurrence is sharp whenever each independent `i`-set has exactly
  `m+d-i` extensions.
* Knowing `I⊆D` does not force the cluster denominator `a-|D|` to be large: adversarial word
  pairs can have `|D|` close to `a`.  Thus the existing affine-cluster theorem cannot uniformly
  replace `n-d` by a prize-saving factor.
* Summing the sharper denominators without controlling how locked sets overlap simply rewrites
  the same incidence mass; it does not cancel `R_d`.

Verdict: **valid local theorem; global no-go at the choose-ratio wall.**
