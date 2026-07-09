# Design-matrix / affine-cluster attack (2026-07-09)

**Verdict:** one substantive local theorem lands, but the global design-matrix attack does not
close the prize.  A fixed affine cluster of witness polynomials has at most `n` bad scalars (in
fact it obeys a sharper pin-multiplicity inequality).  The missing step is a bound on the number
of clusters, and the first-interior saturation example exhibits many interpolation-pencil
clusters.  This is the existing line-list / higher-order-MDS wall in coefficient-space language.

Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DesignMatrixAffineCluster.lean`.

## 1. Exact coefficient-space incidence system

Let `C = RS[D,k]`, write `x_i = D(i)`, and let

`f_j(X) = a_{j,0} + a_{j,1}X + ... + a_{j,k-1}X^(k-1)`

explain scalar `gamma_j` on a witness `S_j`.  Homogenize the coefficient point and the coordinate
hyperplane as

```
P_j = (1, gamma_j, a_{j,0}, ..., a_{j,k-1})^T in F^(k+2),
h_i = (-u0_i, -u1_i, 1, x_i, ..., x_i^(k-1)) in (F^(k+2))^*.
```

Then the agreement equation is exactly

```
h_i P_j = f_j(x_i) - u0_i - gamma_j u1_i = 0.
```

With `H` the `n x (k+2)` matrix of the `h_i` and `P` the `(k+2) x m` matrix of witness
points, the residual matrix is

```
R = H P = V A - u0 1^T - u1 gamma^T,
rank(R) <= k+2,
R_{i,j} = 0 for i in S_j.
```

Here `V` is the `n x k` Vandermonde evaluation matrix and `A` is the coefficient matrix.

There is also an exact rank reading of the no-joint clause.  Since every `k` rows of `V` are
independent and `P_j` lies in `ker(H_{S_j})`, for `|S_j| >= k`:

```
pairJointAgreesOn C S_j u0 u1
  iff u0|S_j and u1|S_j are both in col(V_{S_j})
  iff dim ker(H_{S_j}) >= 2.
```

Consequently, for an MCA witness,

```
not pairJointAgreesOn C S_j u0 u1
  iff rank(H_{S_j}) = k+1
  iff ker(H_{S_j}) = span(P_j).
```

Thus the coefficient points are high-multiplicity *simple projective vertices* of this special
hyperplane arrangement.  This is the precise bipartite/design-matrix constraint; no genericity
has been inserted.

## 2. Proven affine-cluster law

Suppose a subfamily lies on one nonvertical affine line, so its explainers are
`c0 + gamma c1` for fixed codewords `c0,c1`.  Let

```
D = {i : c0_i = u0_i and c1_i = u1_i}.
```

Coordinates in `D` contain the entire affine line.  At every coordinate outside `D`, agreement
with the line pins at most one scalar.  A witness of size at least `a` supplies at least
`a - |D|` such pins when `|D| < a`.  When `|D| >= a`, the ordinary heavy-pencil argument is
silent, but the MCA no-joint clause still forces at least one pin.  Double counting gives

```
max(1, a - |D|) * |G| <= |supp(u1-c1)| <= n.
```

This is proved by
`DesignMatrixAffineCluster.affineCluster_card_mul_le_support`; the `|G| <= n` corollary is
`affineCluster_card_le_length`.  `affineClusterBadScalars` fixes the existential codeword in the
actual `mcaEvent` definition to the pencil `c0 + gamma c1`, and
`affineClusterBadScalars_subset_mcaEvent` proves that this is a genuine MCA-bad subfamily, not a
detached incidence surrogate.

Duplicate audit: `BadGammaAffineCount.badGamma_affine_card_le` and
`HighMultiplicity.card_highMult_mul_le` supply the root-count engine, while
`Frontier._SpreadExcessLaw.pencilHeavyScalars_card_le` already handles the branch `|D| < a`
without using no-joint.  The new content is the uniform `max(1, ...)` law, especially the formerly
excluded saturated branch `|D| >= a`, and its direct `mcaEvent` interface.

## 3. Exact n=8 counterexample to a small cluster cover

This is a finite exact-arithmetic probe, not a Lean-certified concrete instance.

```
p = 4129 (prime), omega = 777, ord(omega) = 8,
D = [1,777,895,1743,4128,3352,3234,2386],
k = 2, a = 3, delta = 5/8,
u1_i = x_i^2,
u0 = [3968,2852,3462,333,3333,2288,946,1570].
```

For each triple `S={i,j,l}`:

1. interpolate `u0` and `u1` on `T={i,j}` by linear polynomials `I_T(u0), I_T(u1)`;
2. set
   `A = u0_l - I_T(u0)(x_l)`, `B = u1_l - I_T(u1)(x_l)`;
3. `B != 0` because no linear polynomial agrees with `X^2` at three distinct field points;
4. set `gamma_S = -A/B` and
   `f_S = I_T(u0) + gamma_S I_T(u1)`.

Exact enumeration gives:

```
56 triples, 56 distinct gamma_S, 56 distinct points P_S=(gamma_S,coeff(f_S));
each gamma has exactly one witness triple.
```

These are **actual MCA-bad scalars**, not merely explainable scalars: `f_S` is a codeword agreeing
on `S`, the relative threshold is exactly `|S|/8 = 3/8`, and the no-joint clause holds because a
joint direction codeword would be linear and agree with `X^2` on all three points, impossible by
the degree-2 root bound.

The affine-line census of the 56 coefficient points is:

```
28 rich lines of size 6; every other determined line has size 2; maximum cluster size = 6.
```

The 28 rich lines are not accidental.  For each two-subset `T`, the interpolation pencil

```
L_T = {(gamma, coeff(I_T(u0) + gamma I_T(u1))) : gamma in F_p}
```

contains exactly the six points `P_S` with `T subset S`.  Each point lies on its three lines
indexed by the two-subsets of `S`.  Therefore any affine-line cover needs at least
`ceil(56/6)=10` lines, even though every individual cluster satisfies the new theorem sharply at
`n-k=6`.

This reproduces the generic singleton saturation recorded in
`Frontier/FirstInteriorLevelDirectionBlind.lean` and `Frontier/_SecondWitnessFloor.lean`, now with
the coefficient-space line arrangement made explicit.

## 4. Why the design-matrix rank step stops

For each coordinate `i`, the incident witness points lie in the `k`-dimensional hyperplane
`h_i^perp`.  A forced local linear dependence therefore needs `k+2` points.  At constant rate this
support size is `Theta(n)`, so a generic design-matrix rank bound loses exactly the factor needed
near `m = Theta(n)`.  Worse, the work is over `F_p`; the positive-semidefinite/diagonal-dominance
step in characteristic-zero design-matrix proofs is not available for arbitrary finite-field
dependency coefficients.

Equivalently, every `k`-subset of a witness defines an interpolation pencil.  A bad point owns
`choose(a,k)` such pencils, but the ambient family has `choose(n,k)` members and one pencil may
carry up to the cluster bound above.  The resulting count is still of the field-blind form

```
|bad| * choose(a,k) <= O(n) * choose(n,k),
```

which is exponential in the constant-rate window.  Reducing the number of occupied pencils is
precisely the higher-order-MDS / line-list obligation.  On the smooth dyadic domain, order-3
higher-MDS already fails (`HigherOrderMDSOrderThreeFail.lean`), and the relaxed corank is linear in
the agreement scale (DISPROOF_LOG C21/C24/P7).  No new cluster-number bound survived this attack.

**Net:** keep the affine-cluster theorem as a reusable local bound.  Do not advertise the
design-matrix representation as a prize closure; globally it is a new coordinate system for the
existing line-list/higher-order-MDS wall.
