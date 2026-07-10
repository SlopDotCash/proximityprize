# Syndrome--Kronecker pencils for the MCA bad-scalar count (2026-07-09)

## Verdict

The Reed--Solomon syndrome sequence gives an exact affine Hankel pencil for every
MCA explanation.  Kronecker theory then gives a genuinely sharp fixed-domain
split-fibre theorem in the **one-right-minimal-index** case: an `m x (m+1)` linear
pencil has at most `n` isolated parameters whose kernel contains a degree-`m`
locator split over a fixed `n`-point domain.  The proof counts roots of the
primitive minimal kernel vector and charges rank-drop parameters to the regular
part of the Kronecker form.  It is saturated by the two-clique/bisimplex packing.

At the tight-budget predecessor

```text
e = n/2 - 1,     agreement = n/2 + 1,
```

the syndrome pencil has generic right nullity exactly `k-1`.  Thus the sharp
one-corank theorem applies directly only when `k=2`.  For `k>2`, eliminating the
moving `(k-1)`-plane of locators requires `(k-1)`-st compounds.  Even under the
best possible full-spark hypothesis this gives

```text
    #gamma <= c * C(n,k-1) / C(e,k-1),
```

which is about `c * 2^(k-1)` at the half predecessor.  Near capacity, with excess
`m ~ n/log n`, the analogous ratio is `exp(Theta(n))`.  Vandermonde evaluation by
itself does not improve the local compound density: on a prescribed set of points,
an arbitrary linear code/matroid is realizable by a polynomial subspace.

So the route cleanly recovers the dimension-two edge and explains the obstruction,
but Kronecker/compound theory alone does not close the production good side.  The
missing input is precisely a rigidity theorem for **domain-supported points in a
moving kernel scroll**.  On the smooth domain this is the existing
elementary-symmetric/PTE/curve-decodability core in a new geometric form.

## 1. Exact syndrome--locator dictionary

Let `alpha_1,...,alpha_n` be distinct points of a field `F`, let

```text
Z_D(X) = product_i (X-alpha_i),       D = n-k,
v_i    = 1 / Z_D'(alpha_i),
```

and define the `D` Reed--Solomon syndromes of a word `u` by

```text
s_j(u) = sum_i v_i alpha_i^j u_i,     0 <= j < D.                 (1)
```

The Lagrange leading-coefficient identity gives `s_j(f(alpha))=0` for every
`deg f < k`: indeed `deg(X^j f) <= n-2` for `j<D`.  Hence `(s_j)` is a parity-check
map for `RS(alpha,k)`.

For a support `E`, `|E|=h`, write

```text
Lambda_E(X) = product_{i in E}(X-alpha_i) = sum_{l=0}^h lambda_l X^l.
```

Let `U_E` be the span in syndrome space of the `h` evaluation columns supported on
`E`.  The following equivalence is exact:

```text
s in U_E
  iff  sum_{l=0}^h lambda_l s_{j+l} = 0  for 0 <= j < D-h.       (2)
```

Proof: the right side says that `s` is orthogonal to the coefficient vectors of

```text
Lambda_E, X Lambda_E, ..., X^(D-h-1) Lambda_E.
```

Those `D-h` polynomials are independent and vanish on `E`, so they are exactly
`U_E^perp`.

For a stack `u_0,u_1`, put `s_a=s(u_a)` and define the affine Hankel pencil

```text
P_h(gamma)_{j,l} = (s_0)_{j+l} + gamma (s_1)_{j+l},
0 <= j < D-h,  0 <= l <= h.                                    (3)
```

Then

```text
u_0 + gamma u_1 is within h errors of RS on support E
  iff P_h(gamma) lambda(E) = 0.                                 (4)
```

For that same support, the MCA non-joint clause is exactly

```text
P_h^(1) lambda(E) != 0,                                         (5)
```

where `P_h^(1)=H_h(s_1)`.  Indeed, pairwise joint agreement on the complement of
`E` is equivalent to `s_0,s_1 in U_E`.  Under (4), membership of `s_1` in `U_E`
also forces membership of `s_0`; therefore non-jointness is precisely (5).  In
particular each accepted support determines at most one scalar.

If a witness has fewer than the allowed number of errors, one can pass to an exact
error-size witness without losing non-jointness whenever the agreement threshold is
at least `k+1`: one of the two rows is not degree-`<k`-interpolable on the original
agreement set, hence already fails on some `(k+1)`-subset; retain that subset and
extend it to the desired exact agreement size.  Thus the exact-size pencil is the
right object at the half predecessor.

## 2. The one-corank split-fibre theorem

Here is the clean abstract statement suggested by (3).

### Theorem (isolated split fibres of a one-corank linear pencil)

Let `Omega subset F` contain `n` distinct points.  Let

```text
P(T) = A + T B in Mat_{m x (m+1)}(F[T])
```

have normal row rank `m`.  Identify a vector `q=(q_0,...,q_m)` with
`Q_q(X)=sum_j q_j X^j`.  Count parameters `t in F` for which there is a nonzero
`q` satisfying

```text
P(t)q = 0,
Bq != 0,                                                        (6)
Q_q has m distinct roots in Omega.                              (7)
```

Then the number of such parameters is at most `n`.

### Proof

The Kronecker form of a full-row-rank `m x (m+1)` pencil has one right singular
block of minimal index `mu` and a regular part of total size

```text
d = m-mu.                                                       (8)
```

Let

```text
q(T) = q_0 + q_1 T + ... + q_mu T^mu
```

be the primitive minimal kernel vector.  Its coefficient vectors
`q_0,...,q_mu in F^(m+1)` are linearly independent (they are a constant change of
basis of the standard `L_mu` kernel vector).  Away from the finite eigenvalues of
the regular part, `ker P(t)` is the line spanned by `q(t)`.  There are at most `d`
finite rank-drop parameters.

Form the bivariate locator

```text
Q(T,X) = sum_{j=0}^m q_j(T) X^j.
```

Let `Z subset Omega` be the set of fixed vertical roots,

```text
Z = {alpha in Omega : Q(T,alpha) is identically zero},
z = |Z|.
```

The `z` independent evaluation conditions cut the degree-`<=m` coefficient space
to dimension `m+1-z`.  Since all `mu+1` independent coefficient vectors of `q(T)`
lie in this subspace,

```text
mu <= m-z.                                                      (9)
```

At a regular accepted parameter, (6) makes the supported locator proportional to
`q(t)`, and (7) supplies at least `m-z` non-fixed incidences
`Q(t,alpha)=0`.  For every `alpha notin Z`, the nonzero polynomial
`Q(T,alpha)` has degree at most `mu`.  Hence, if `M_reg` is the regular count,

```text
M_reg (m-z) <= (n-z) mu.                                       (10)
```

If `z=m`, then (9) gives `mu=0`; the projective kernel locator is fixed and (6)
fails at every regular parameter, so only rank drops remain.  Otherwise combine
(8)--(10):

```text
M <= d + (n-z)mu/(m-z)
  =  m-mu + (n-z)mu/(m-z)
  <= n.                                                        (11)
```

The final inequality is equivalent to

```text
(n-m) * (1 - mu/(m-z)) >= 0,
```

using `n>=m` and (9).  This proves the claim.

The role of isolation in (6) is essential.  Without it, a fixed domain-split
kernel vector in `ker A intersect ker B` would be accepted for every parameter.
That is exactly a common-support/joint-agreement fibre, which MCA removes.

## 3. Why `X-gamma^2` is not a counterexample at corank one

For a general bivariate polynomial of `X`-degree `w` and parameter degree `a`, the
elementary vertical-incidence bound is only

```text
#split fibres * (w-z) <= a (n-z).                              (12)
```

Thus `K(gamma,X)=X-gamma^2` can have up to `2n` domain-root fibres: it has
`w=1`, `a=2`, `z=0`.

It cannot be the primitive locator kernel of a one-corank **linear** pencil.  A
right minimal vector of index `2` has three linearly independent coefficient
vectors and therefore needs at least three active locator coordinates.  More
generally, after removing `z` fixed roots, Kronecker theory forces exactly the
inequality `a=mu <= w-z` used in (11).  This is the geometric fact missing from a
raw bivariate root count.

This exclusion is special to a canonical one-dimensional kernel.  In higher
corank one may choose a parameter-dependent point inside a moving kernel plane;
the chosen section can have degree larger than every individual minimal index.
There is then no canonical low-degree `K(gamma,X)` to which (12) can be applied.

## 4. Coding parameters at the tight half predecessor

At

```text
h=e=n/2-1,      D=n-k,
```

the pencil (3) has

```text
c = D-h = h-k+2 rows,
h+1 columns,
generic right nullity r = (h+1)-c = k-1.                       (13)
```

Consequently `k=2` is exactly the one-corank case: `c=h`.  On the normal-full-rank
branch, the theorem above gives `#bad <= n`, matching the prize budget at the
predecessor.  This is a matrix-pencil explanation of the sharp dimension-two edge,
not a replacement for the existing unconditional UDR2 theorem: a full MCA proof
must also dispatch pencils whose normal rank is below `h`, which the existing UDR2
argument already does.

For every production dimension `k>2`, (13) is the obstruction: the supported
locator is a point in a moving projective `(k-2)`-plane rather than the value of one
canonical bivariate polynomial.

## 5. The exact higher-corank compound bound

The loss can be stated precisely.  Let

```text
P(T) in Mat_{c x (c+r)}(F[T])
```

be a linear pencil of normal row rank `c`.  Let `Q(T)` be a right minimal basis
with column minimal indices `mu_1,...,mu_r`; put

```text
mu = sum_j mu_j.
```

If the regular part has size `d`, Kronecker bookkeeping gives

```text
d + mu = c.                                                     (14)
```

Interpret the columns of `Q(T)` as the coefficients of `r` locator polynomials.  For
each domain point `alpha`, let `v_alpha(T)` be their evaluation row.  For an
`r`-subset `I` of the domain, set

```text
Delta_I(T) = det(v_alpha(T))_{alpha in I}.
```

Every nonzero `Delta_I` has degree at most `mu`.  Let `B` be the collection of
`I` for which `Delta_I` is not identically zero, and suppose every accepted
`h`-support `E` contains at least

```text
beta <= #{I subset E : |I|=r and I in B}                       (15)
```

generic bases.  At a regular accepted parameter, a domain-supported locator is
`Q(t)a`; its `h` root rows annihilate `a`, so every `r`-minor inside `E` vanishes.
Double-counting roots of the compounds and adding the `d` rank-drop parameters gives

```text
#accepted parameters <= d + mu * |B| / beta.                   (16)
```

Condition `beta>0` is automatic for an MCA-isolated support.  If every `r`-minor on
`E` vanished identically, there would be a rational kernel section vanishing on all
`h` points.  Since a degree-`<=h` polynomial with those `h` roots is a scalar multiple
of `Lambda_E`, this would put the fixed locator in `ker A intersect ker B`, contradicting
the non-joint condition.

In the ideal full-spark case, `B` is every `r`-subset and

```text
beta = C(h,r),
#accepted <= d + mu C(n,r)/C(h,r)
          <= c C(n,r)/C(h,r).                                  (17)
```

This is the best direct compound-root count.  The factor is not a loose arithmetic
artifact: eliminating a point of `P^(r-1)` requires an `r x r` minor, so a bad
`h`-set contributes `C(h,r)` roots among `C(n,r)` possible compounds.

Vandermonde evaluation does **not** force full spark for the moving minimal-basis
subspace.  Evaluation of degree-`<h` polynomials on a prescribed `h`-set is an
isomorphism, so an arbitrary representable rank-`r` matroid can occur as the
evaluation matroid of an `r`-dimensional polynomial subspace.  Even with no loops,
the universal local lower bound is only `h-r+1` bases (a basis plus one replacement
per extra element), far too small.  Common polynomial factors create loops and make
the density still worse.

## 6. Quantitative failure at the two target regimes

### (a) Tight-budget predecessor, `k<=n/4`

Here `h=n/2-1`, `r=k-1`, and `c=h-k+2`.  Formula (17) is approximately

```text
c * (n/h)^(k-1) ~= c * 2^(k-1).                                (18)
```

It is sharp enough when `k=2`, but exponentially above the desired `n` ceiling as
soon as `k` is a positive fraction of `n`.  Replacing full spark by the actual local
base count can only weaken it.

### (b) Near capacity, excess `m~n/log n`

Write

```text
D=(1-rho)n,
h=D-m,
c=m,
r=h+1-c=D-2m+1.
```

Then

```text
log C(n,r)            = n H(r/n) + O(log n) = Theta(n),
log C(h,r)=log C(h,m-1) = O((n/log n) log log n)=o(n).
```

Therefore

```text
C(n,r)/C(h,r) = exp(Theta(n)),                                 (19)
```

and (17) is exponentially larger than the `Theta(n)` tight field-normalized budget.
The fact that most right minimal indices are zero does not fix this: it reduces the
degree `mu` to at most `m`, but it does not remove the exterior-dimension ratio.

## 7. Red-team: the overlap/bisimplex packing

At the half predecessor, write `n=2h+2` and partition the domain into
`S_1 disjoint_union S_2`, each of size `h+1`.  The bisimplex stack is

```text
u_1 = 1 on S_1, 0 on S_2,
u_0 = alpha on S_1, 0 on S_2.
```

On a root-of-unity domain, the syndrome sequences satisfy the shift identity

```text
(s_0)_j = (s_1)_{j+1}.                                        (20)
```

For every `x in S_1`, the scalar `gamma=-x` has locator
`Lambda_{S_1\{x}}`; for every `x in S_2`, it has locator
`Lambda_{S_2\{x}}`.  Thus the `n` bad scalars are two complete locator cliques.
Equation (20) puts all of them in the same affine Hankel pencil, and (5) is nonzero:
they are genuine isolated MCA fibres, not common-support artefacts.

For `k=2` this saturates the one-corank theorem.  For `k>2` it is entirely consistent
with (17), whose ceiling is already exponentially larger than `n`.  Hence the packing
does not refute the pencil route; it proves that any successful higher-corank
sharpening must recognize and charge complete locator cliques rather than merely count
compound roots.

The tuned overlap packing at the next radius supplies `n+2` split fibres.  This is also
consistent with the geometry: increasing the error degree by one increases the generic
right nullity from `k-1` to `k+1`, so the one-corank `n` theorem no longer applies.

## 8. Relation to the in-tree WB pencil

`WBPencilWindowMatrix.lean` and `WBPencilWindowLaw.lean` already build a larger linear
pencil in `(Z,Q,h)` and, under an adjugate anchor, obtain a canonical Cramer locator
`K(gamma,X)`.  Their current root union bound treats each domain polynomial separately
and pays `n(w+1)`.

The theorem above suggests a possible sharpening on a **primitive one-corank branch**:

1. divide the Cramer column by the gcd of its maximal minors;
2. separate finite rank-drop parameters;
3. factor the fixed domain roots of its locator component;
4. prove that the locator projection of the minimal kernel block retains the
   coefficient-rank property `parameter degree <= moving locator degree`;
5. apply (10) instead of a raw union bound.

Step 4 is automatic for the pure syndrome pencil because all columns are locator
coefficients.  It is **not automatic** for the WB pencil: its `Q` and `h` blocks can
carry the independent Kronecker coefficient vectors even when the locator projection
has small moving `X`-degree.  A proof needs the reduced-representation degree/coprimality
constraints to show that projection is a minimal-basis embedding.  Without that lemma,
claiming an `n` bound for the WB Cramer locator would be unsound.

The elementary vertical-incidence part, including the `a <= h-z` corollary, is now
machine-checked in
`Frontier/_SyndromePencilSplitFiberCount.lean`.  Formalizing the one-corank theorem
itself is not currently cheap: Mathlib has no Kronecker canonical-form/minimal-index
API, so (8), coefficient-vector independence, and the regular-part charge would first
need a new polynomial-matrix layer.

## 9. The remaining theorem-shaped target

The higher-corank problem is now isolated as follows.

> **Kernel-scroll divisor rigidity.**  Let `Q(gamma)` be the right minimal-basis scroll
> of the Reed--Solomon syndrome Hankel pencil.  Bound the number of parameters for which
> `P(ker Q(gamma))` contains a degree-`h` divisor of `X^n-1`, after deleting fixed
> common-support fibres.  At the half predecessor the sharp conjectural bound is `n`,
> with equality only through a controlled union of locator cliques/packing components.

A theorem of this strength must use more than the Kronecker indices and compound
degrees.  It must exploit the arithmetic of the divisor set of `X^n-1` (equivalently,
the elementary-symmetric fibres of subsets of `mu_n`) or a curve-decodability theorem.
That is exactly where the existing smooth-domain PTE and quotient constructions live.

## 10. Half-predecessor hyperplane arrangement and the joint-core probe

There is a second exact coordinate system for the same predecessor.  Write a codeword
as `p(X)=sum_{j<k} c_j X^j` and put

```text
H_i = {(gamma,c) : p(alpha_i) = u0_i + gamma u1_i} subset F^(k+1).
```

The normal of `H_i` is

```text
(-u1_i, 1, alpha_i, ..., alpha_i^(k-1)).
```

Every `k` normals are independent, because their last `k` coordinates form a square
Vandermonde matrix.  If a point lies on the hyperplanes indexed by `S`, `|S|>=k`,
then

```text
rank{normal(H_i) : i in S} = k
  iff u1|S is a degree-<k evaluation
  iff u0|S and u1|S are jointly degree-<k evaluations.             (21)
```

The last equivalence uses the incident polynomial `p` and
`u0|S=p|S-gamma*u1|S`.  Thus an MCA witness is exactly a `t`-rich arrangement point
whose incident normals have full rank `k+1`, where here `t=n/2+1`.

### A rigorous local line law

For a `k`-set `L`, let

```text
A_L = intersection_{i in L} H_i
```

be its affine line, and let `D_L={i : A_L subset H_i}`, `d=|D_L|`.  If `q` full-rank
`t`-rich points lie on `A_L`, then

```text
d + q * max(1,t-d) <= n.                                      (22)
```

Indeed, every hyperplane outside `D_L` meets `A_L` in at most one point, so the
external incident fibres of distinct points are disjoint.  If `d<t`, each point needs
at least `t-d` external hyperplanes.  If `d>=t`, it still needs one: all normals of
hyperplanes containing `A_L` lie in the `k`-dimensional annihilator of the line, while
the point is required to have rank `k+1`.

There is also a useful transverse fact:

```text
y notin A_L  implies  #{i in D_L : y in H_i} <= k-1.           (23)
```

Otherwise any `k` of those hyperplanes have independent normals, and their
one-dimensional intersection is exactly `A_L`, forcing `y in A_L`.  Distinct core
lines consequently have core intersection at most `k-1`.

Equations (22)--(23) are the clean joint-core/external-intersection lever requested by
the arrangement picture.  They do not by themselves sum to a global `n` bound: a
point lies on `C(t,k)` interpolation lines, and the naive line census again pays the
exponential `C(n,k)/C(t,k)` factor.

### Multiple half-core splines

The most dangerous way to saturate (22) is a joint core `C` of size `t-1=n/2`.
Let `a_C,b_C` be the degree-`<k` polynomials agreeing with `u0,u1` on `C`.  Every
external coordinate with nonzero direction defect gives a genuine non-joint rich
point at

```text
gamma(C,i) = -(u0_i-a_C(alpha_i))/(u1_i-b_C(alpha_i)).          (24)
```

Two complementary half-cores give the known `n`-scalar packing.  Trying three or
more cores is not a free set-packing construction: the core polynomials must define
the same two words on all overlaps.  If `i` lies in a second core `E`, (24) becomes

```text
gamma(C,i) = -(a_E-a_C)(alpha_i)/(b_E-b_C)(alpha_i),            (25)
```

and the polynomial differences over a cycle of cores satisfy a cocycle/syzygy
identity.  In the common rank-one case, compatible deviations have the form
`A(X)v` and `R(X)v`; then every cross-core scalar collapses to the single global
rational map

```text
gamma(i) = -A(alpha_i)/R(alpha_i),                              (26)
```

so it is chargeable to the coordinate `i`, independent of which core produced it.

There is a complete theorem for the architecture that contains the known equality
packing.  Suppose `A,B` are complementary half-cores and `k<=n/4`.  On `A` the two
rows have polynomial templates `(a_A,b_A)`, and on `B` they have templates
`(a_B,b_B)`.  Let `C` be any further half-core.  Since

```text
|C intersect A| + |C intersect B| = n/2,
```

one of the intersections has size at least `n/4>=k`.  If, say,
`|C intersect A|>=k`, polynomial uniqueness forces

```text
(a_C,b_C)=(a_A,b_A).                                          (27)
```

The `C`-defect is therefore zero on `A\C`, while on `B\C` it is exactly the already
existing `A`-defect.  Moreover, compatibility on `B intersect C` kills those
corresponding `A`-defects.  The case with a `B` majority is symmetric.  Thus every
additional half-core only deletes or repeats projective defect directions; it can
never add one.  Consequently:

> **Complement-anchored half-core theorem.**  If a compatible half-core family contains
> a complementary pair and `k<=n/4`, all core-plus-one rich points in the family induce
> at most `n` scalars.  Equality can already be attained by the complementary pair.

This argument uses only distinct evaluation points and degree-`<k` uniqueness, not the
root-of-unity structure.  It rigorously excludes the most direct way of adding a third
clique to the bisimplex packing.

The exact probe
`scripts/probes/probe_half_predecessor_joint_cores.py` tests the first nontrivial
case `n=16,k=4` over `mu_16 subset F_97`.  For a core family `F`, it constructs the
linear spline space

```text
W(F) = {u : u|C is degree-<4 for every C in F}
```

and the external defect functionals
`delta_(C,i) : W(F)/RS_4 -> F`.  Proportional defect functionals induce the same
ratio (24) for **every** choice of `u0,u1`; hence the number of their nonzero
projective directions is an exact, row-independent ceiling for this architecture.

Starting from the complementary cores `{0,...,7}` and `{8,...,15}`, the computation
is:

```text
two cores:  dim(W/RS)=4, projective-defect ceiling = 16, attained;
all 12,868 possible third cores:
  1,696 retain dim(W/RS)>=2,
  maximum projective-defect ceiling = 15;
fourth-core extensions of the eight strongest triples:
  2,584 admissible extensions, maximum ceiling = 15;
6,000 arbitrary-pair/mutated-third stress trials:
  maximum ceiling = 15.
```

Thus the attempted `>16` construction failed for a structural reason stronger than
random-search failure: in the exhaustive anchored three-core family, the projective
defect matroid itself has at most `15` points.  The two-core packing remains the unique
maximizer seen by the probe.  For the complementary anchor, the general argument
(27) now explains the computation; the fourth-core enumeration is a redundant check.
The arbitrary-anchor statement remains a stress test, not an exhaustive theorem.

This suggests a precise intermediate target.

> **Half-core spline direction bound.**  For any compatible family of half-domain
> Reed--Solomon cores, the union of projective external-defect functionals on
> `W(F)/RS_k` has size at most `n`.

Such a theorem would rule out all multiple-joint-core counterexamples and explain
the bisimplex equality case by a coordinate charge such as (26).  It would still
need a core-extraction argument to cover full-rank `t`-rich points that do not lie on
a `(t-1)`-core line.  These are now the two exact arrangement-side gaps: spline
direction rigidity for large cores, and reduction of the remaining small-core
stratum using (22)--(23).
