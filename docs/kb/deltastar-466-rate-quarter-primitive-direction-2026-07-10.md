# Delta-star #466: primitive-direction collapse at rate one quarter

Date: 2026-07-10

Status: new axiom-clean algebraic strengthening.  This does **not** close the
global rate-quarter half-predecessor bound.  It removes the artificial
reference-slope root loss from every determinant-collapsed cluster and
sharpens the remaining high-core obstruction to literal cross-core isolation.

## 1. The common-factor defect in the raw ratio

For distinct reference polynomial pairs

```text
c0 = (a0,r0),   c1 = (a1,r1),
d  = c1-c0 = (a1-a0,r1-r0),
```

the earlier collapsed-cluster injection used

```text
gamma(x) = -(a1-a0)(x)/(r1-r0)(x).
```

It therefore required `(r1-r0)(x) != 0` at every chosen petal coordinate.
A degree bound discarded up to `k-1` roots and forced a supply of `k` fresh
coordinates per scalar.

That loss is not intrinsic.  The two components of `d` may share a polynomial
factor `H`; at a root of `H`, the raw reference vector is zero and its ratio is
the wrong chart.  Divide the factor out:

```text
H = gcd(a1-a0,r1-r0),
A = (a1-a0)/H,
R = (r1-r0)/H.
```

Because `c0 != c1`, `H != 0`, and `gcd(A,R)=1`.

## 2. Polynomial, not merely rational, collinearity

If a line `c=(a,r)` is determinant-collapsed with the references, then

```text
(a1-a0)(r-r0) = (r1-r0)(a-a0).
```

Cancellation of the nonzero `H` gives

```text
A(r-r0) = R(a-a0).                                      (1)
```

Since `A` and `R` are coprime, Euclid's lemma strengthens (1) to an actual
polynomial factorization

```text
there exists f in F[X] such that
  a-a0 = A f,
  r-r0 = R f.                                            (2)
```

Thus a collapsed cluster lies on one affine `F[X]`-line.  The usual statement
of affine collinearity over `F(X)` is strictly weaker than the form available
here.

This is formalized in
`Frontier/_HalfPredecessorRateQuarterPrimitiveDirection.lean`:

* `primitiveDirection_isCoprime`;
* `primitive_relation_of_lineDeterminant_eq_zero`;
* `exists_polynomial_factor_of_lineDeterminant_eq_zero`.

## 3. Every transverse petal is automatically in the slope chart

Let two cluster lines have difference `(da,dr)`.  Subtracting their two copies
of (1) gives

```text
A dr = R da.                                             (3)
```

At a transverse cross-core petal, `dr(x) != 0`.  If `R(x)=0`, (3) forces
`A(x)=0`; this contradicts coprimality, because coprime polynomials cannot
vanish simultaneously at a field point.  Hence `R(x) != 0` automatically.
The petal equation

```text
da(x) + gamma dr(x) = 0
```

then gives

```text
gamma = -A(x)/R(x).                                      (4)
```

The right side depends only on the coordinate, not on the source line, target
line, or polynomial factor `f`.  Assigning one fresh cross-core coordinate to
each scalar is therefore injective, and the whole assigned collapsed cluster
has at most `n` scalars.

The axiom-clean Lean endpoints are:

* `primitiveSlope_eval_ne_zero_of_pair_slope_eval_ne_zero`;
* `gamma_eq_primitiveScalarAt_of_pairEquation`;
* `card_le_domain_of_primitive_collapsed_fresh_petals`.

The previous explicit hypothesis that chosen coordinates avoid roots of the
raw reference slope is gone.

## 4. High-core consequence

`Frontier/_HalfPredecessorRateQuarterPrimitiveHighCore.lean` composes the
primitive injection with the existing three-half-core determinant collapse.
The quantitative requirement

```text
k fresh cross-core coordinates per scalar
```

becomes

```text
one nonempty fresh cross-core fibre per scalar.
```

The family-level theorem
`card_le_two_mul_of_distinct_half_core_nonempty_fresh_target_supply` proves the
domain bound from that one-coordinate supply.  The resulting exact trichotomy
`card_le_or_uncovered_or_half_core_isolated_scalar` is:

```text
|G| <= n;
or some scalar lies on no relevant half-core line;
or a scalar lies on a half-core source whose fresh fibre into every
   relevant half-core target is empty.
```

There is no separate raw equal-slope branch and no `k-1` exceptional-root
branch.  Equal-slope clusters are not silently solved: they reappear honestly
as the isolation outcome, because (3) makes every cluster slope difference
zero and hence forbids transverse fresh fibres.

The core-union version is in
`Frontier/_HalfPredecessorRateQuarterPrimitiveClusterAssembly.lean` as
`card_le_domain_of_primitive_collapsed_clusterCoreUnion`.  It removes the same
root-avoidance hypothesis from the existing coverage-based assembly theorem.

## 5. Red-team audit and remaining recursion

The primitive invariant bounds a **whole collapsed cluster** only after every
counted scalar receives a fresh coordinate carried by another line in that
cluster.  It does not prove that such a target core exists.

For a selected scalar on a source line, no-jointness guarantees at least one
agreement coordinate outside the source core.  That coordinate need not lie
in any half-core target.  At such an isolated coordinate the equation is

```text
(a0-u0)(x) + f_source(x) A(x)
  + gamma ((r0-u1)(x) + f_source(x) R(x)) = 0,
```

whose solution depends on the source factor `f_source(x)`.  Therefore the
coordinate-only injection (4) is unavailable.  This supplies a direct
countercheck against the unjustified claim that determinant collapse alone
bounds every cluster.

The next honest target is the isolated population.  Two possible continuations
retain more structure than cardinal-only petal selection:

1. show that more than `n` selected points force one isolated fresh coordinate
   to be shared with another selected agreement set; the corresponding secant
   core then supplies a target, and one asks when it must enter the half-core
   cluster;
2. stratify isolated coordinates by the values `f_source(x)`.  Equation above
   is a fractional-linear map in that value, while degree bounds constrain the
   evaluation vectors of the factor polynomials.  This is a lower-degree
   recursion on the cluster factors, not another raw set-system moment bound.

Neither continuation is presently proved, so the global rate-quarter case
remains open.

### A landed lower-degree bridge

The algebraic half of continuation 2 is now formal in
`Frontier/_HalfPredecessorRateQuarterPrimitiveFactorRecursion.lean`.
Choose Bezout polynomials `pA+qR=1`, put

```text
v0(x)=u0(x)-a0(x),  v1(x)=u1(x)-r0(x),
t(x)=p(x)v0(x)+q(x)v1(x),
B={x : A(x)v1(x)-R(x)v0(x)=0}.
```

Then the module proves the exact common-word identity

```text
D_f = B intersect {x : f(x)=t(x)}.
```

This is `jointCore_eq_masked_factor_agreement`: all cluster cores are literal
Reed--Solomon agreement sets for their factors on one shared received word,
restricted by one shared mask.

If cluster lines have factors `f` and `g`, coprimality gives the exact
implication

```text
c_f(x)=c_g(x)  =>  f(x)=g(x).
```

Consequently

```text
|D_f intersect D_g| <= deg(f-g),
```

and degree-`<ell` factors give the RS cap `ell-1`.  The reusable Lean
endpoints are
`core_intersection_card_le_factor_sub_natDegree` and
`core_intersection_card_le_factor_dimension_pred`.

Moreover, if a nonzero primitive component has degree `d`, then any nonzero
factor occurring in a degree-`<k` cluster line has degree `<k-d`; this is
`factor_natDegree_lt_sub_of_component_factor`.  Thus primitive directions of
degree at least `k/2` descend the cluster-line core geometry to effective
dimension at most `k/2`, the already tractable rate-`1/8` side.  What remains
to make this a complete recursion is to transport the *isolated selected
point population*, not only the cluster-core intersections, into that factor
code.

## 6. Validation

The four new modules pass `scripts/pg-iterate.sh`; the primitive-direction
module also passes the locked project build.  Their axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
