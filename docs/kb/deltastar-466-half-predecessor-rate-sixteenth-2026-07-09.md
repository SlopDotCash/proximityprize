# A half-predecessor good theorem at rate at most `1/16`

Date: 2026-07-09  
Campaign: #466  
Status: paper proof, with the finite incidence/numeric core being formalized separately

## 1. Result

Let `F` be any field, let `alpha_1,...,alpha_n` be distinct elements of `F`, and let
`RS(alpha,k)` be the length-`n`, dimension-`k` Reed--Solomon code.  Assume

```text
n = 2h,      1 <= k,      16k <= n,
```

and put `t = h+1`.  For every two-row stack `(u0,u1)`, at most `n` scalars `gamma` admit a
degree-`< k` polynomial `q_gamma` which agrees with `u0+gamma u1` on at least `t`
coordinates and whose agreement is not jointly explained by two degree-`< k`
polynomials.  Equivalently,

```text
# { gamma : mcaEvent RS (1/2 - 1/n) u0 u1 gamma } <= n.
```

The overlapping packing with `c=0` attains `n`, so the count is sharp.  This proves the
matching good side at the lattice predecessor of `1/2` for the prize rate `rho=1/16`, over
an arbitrary distinct evaluation domain.  It does not use multiplicative-subgroup structure.

The proof is an incidence theorem for rich points in a Vandermonde hyperplane arrangement.
The constant `1/16` is where a line-richness dichotomy leaves every rich affine line with at
most four selected points; a third-moment count then closes with strict slack.

## 2. Lift to rich points and choose full agreement sets

Fix a stack and let `Gamma` be its bad scalars.  For each `gamma in Gamma`, choose one event
witness polynomial `q_gamma` of degree `< k`.  Replace the event's witness set by the **full**
agreement set

```text
A_gamma = { i : q_gamma(alpha_i) = u0_i + gamma u1_i }.
```

Then `|A_gamma| >= t`.  Moreover the pair is still not jointly explained on `A_gamma`: a
joint explanation on the full set would restrict to one on the original event witness.

Write a degree-`< k` polynomial by its coefficient vector `c(q) in F^k` and associate the
affine point

```text
P_gamma = (gamma, c(q_gamma)) in F^(k+1).
```

The points are distinct because their first coordinates are distinct.  Coordinate `i` defines
the affine hyperplane

```text
H_i = { (gamma,c) : sum_{j<k} c_j alpha_i^j = u0_i + gamma u1_i }.
```

Thus `i in A_gamma` exactly when `P_gamma in H_i`, and every selected point is incident to at
least `h+1` of the `2h` hyperplanes.

For completeness, non-jointness is the full-rank condition on these incidences.  On a set of at
least `k` distinct evaluation points the Vandermonde columns have rank `k`.  The displayed
hyperplane relation gives one dependence among the lifted rows

```text
(u0_i, u1_i, 1, alpha_i, ..., alpha_i^(k-1)).
```

There is a second independent dependence exactly when `u0` and `u1` are both degree-`< k`
on that set.  Hence an event witness has affine rank `k+1`.  The proof below only needs the
more elementary consequence that a nonzero degree-`< k` polynomial has at most `k-1` roots.

Put

```text
d = k-1.
```

The rate hypothesis gives

```text
8d <= h-8.                                      (R)
```

In particular `h >= 8`.

## 3. Exact geometry of a collinear family

Consider an affine line `ell` containing at least two selected points.  It cannot be vertical:
two selected points have different `gamma` coordinates.  Therefore there are degree-`< k`
polynomials `a_ell,r_ell` such that all selected points of the line have the form

```text
(gamma, a_ell + gamma r_ell).
```

Define its joint core

```text
D_ell = { i : u0_i = a_ell(alpha_i) and u1_i = r_ell(alpha_i) },
z_ell = |D_ell|.
```

For two distinct selected points `P_gamma,P_beta` on `ell`, subtracting their two agreement
equations gives

```text
(gamma-beta)(u1_i-r_ell(alpha_i)) = 0.
```

Consequently

```text
A_gamma intersect A_beta = D_ell.               (L1)
```

The fresh fibers `A_gamma \ D_ell` are therefore pairwise disjoint as `gamma` varies on the
line.  Each has size at least `t-z_ell` when `z_ell < t`.  When `z_ell >= t`, it still has size
at least one: if it were empty, `(a_ell,r_ell)` would jointly explain the full agreement set,
contrary to the event condition.  If `L_ell` is the number of selected points on `ell`, then

```text
L_ell * max(1,t-z_ell) + z_ell <= 2h.            (L2)
```

In particular every selected affine line has at most `h` points.  Indeed:

* for `z <= h`, `(L2)` gives
  `L <= (2h-z)/(h+1-z) = 1 + (h-1)/(h+1-z) <= h`;
* for `z >= h+1`, it gives `L <= 2h-z <= h-1`.

This includes all degeneracies: the line may have a core larger than the demanded agreement,
and some `q_gamma` may coincide as polynomials, but distinct `gamma` still gives distinct lifted
points and the same subtraction argument.

## 4. Off-line points see a line core in at most `d` positions

Let `P_gamma=(gamma,q_gamma)` be a selected point not on `ell`.  On `D_ell` the received line is
the polynomial line `a_ell+gamma r_ell`.  Hence

```text
A_gamma intersect D_ell
  subset { i : q_gamma(alpha_i) = a_ell(alpha_i)+gamma r_ell(alpha_i) }.
```

The two degree-`< k` polynomials in the last equality are not identical, since identity would put
`P_gamma` on `ell`.  Distinctness of the evaluation domain therefore gives

```text
|A_gamma intersect D_ell| <= d.                  (L3)
```

No assumption on the characteristic is used here.

## 5. Noncollinear triples have codegree at most `d`

For three selected points with distinct scalars `gamma_1,gamma_2,gamma_3`, define the two slope
polynomials

```text
r_12 = (q_1-q_2)/(gamma_1-gamma_2),
r_13 = (q_1-q_3)/(gamma_1-gamma_3).
```

On every coordinate common to all three agreement sets, both slope polynomials equal `u1_i`.
If the three lifted points are noncollinear, `r_12` and `r_13` are distinct.  Their difference is
a nonzero degree-`< k` polynomial, so

```text
|A_1 intersect A_2 intersect A_3| <= d.          (T1)
```

Conversely, if the points are collinear on `ell`, `(L1)` says that this triple intersection is
exactly `D_ell`, of size `z_ell`.

## 6. A large line core forces a two-line configuration

Assume for contradiction that the number `N=|Gamma|` satisfies `N>2h`.  Fix a selected line
`ell`, with core size `z`.  There are at least

```text
N-L_ell >= (2h+1)-h = h+1 >= 3
```

selected points outside it.

For an outside point `P`, `(L3)` and `|A_P|>=t` imply

```text
|A_P intersect D_ell^c| >= t-d.
```

For any three outside points, the elementary three-set inequality inside the universe
`D_ell^c`, of size `2h-z`, gives

```text
|A_P intersect A_Q intersect A_R intersect D_ell^c|
  >= 3(t-d) - 2(2h-z).
```

If

```text
2z > h + 4d - 3,                                 (H)
```

then, using `t=h+1`, the right side is strictly greater than `d`.  By `(T1)`, every triple of
outside points is collinear.  Pick two of them; every further outside point lies on their unique
affine line.  Thus all selected points lie on the union of two affine lines.  Each line has at most
`h` selected points by `(L2)`, so `N<=2h`, a contradiction.

Therefore every selected line in a hypothetical counterexample satisfies

```text
2z <= h + 4d - 3.                                (Hc)
```

Now `(R)` and `(Hc)` imply every selected line has at most four points.  First `(Hc)` puts
`z<t`.  If a line had five points, `(L2)` would give

```text
5(h+1-z)+z <= 2h,
```

or `4z >= 3h+5`.  But doubling `(Hc)` and using `(R)` gives

```text
4z <= 2h+8d-6 <= 3h-14,
```

a contradiction.  Hence

```text
L_ell <= 4                                        (L4)
```

for every line determined by selected points.

This dichotomy is the key new mechanism: a large joint core makes the configuration a union of
two packing lines; avoiding that collapse makes every line so short that the third moment wins.

## 7. Third-moment upper bound

For coordinate `i`, let

```text
m_i = #{ gamma in Gamma : i in A_gamma }.
```

Double counting triples of selected points and incident coordinates gives

```text
T := sum_i C(m_i,3)
   = sum_{unordered triples {P,Q,R}} |A_P intersect A_Q intersect A_R|.   (M1)
```

Noncollinear triples contribute at most `d` by `(T1)`.  A collinear triple on `ell` contributes
`z_ell`; from `(Hc)`,

```text
z_ell-d <= (h+2d-3)/2 <= 5h/8 - 5/2.             (M2)
```

The last inequality is `(R)`.

Let `C_col` be the number of collinear triples.  Every pair of distinct affine points determines
a unique line.  By `(L4)`, for each line with `L` selected points,

```text
C(L,3) = (L-2)/3 * C(L,2) <= 2/3 * C(L,2).
```

Summing over all determined lines gives

```text
C_col <= (2/3) C(N,2).                            (M3)
```

Combining `(M1)`--`(M3)`,

```text
T <= d C(N,3) + (5h/8-5/2) * (2/3) C(N,2).       (U)
```

The use of rational numbers here is only bookkeeping for an integer inequality.

## 8. Third-moment lower bound and the explicit contradiction

The total incidence satisfies

```text
sum_i m_i = sum_gamma |A_gamma| >= N(h+1).
```

The sequence `m -> C(m,3)` is discretely convex.  Balancing the `m_i` therefore minimizes their
sum.  Equivalently, with

```text
a = N(h+1)/(2h),
f(x)=x(x-1)(x-2)/6,
```

the balanced integer lower bound is at least the chord above the convex polynomial `f` on the
interval containing `a`, and hence

```text
T >= 2h f(a).                                     (L)
```

Here `a>h+1>=9`, so only the convex range of `f` is used; zero or low-incidence coordinates cause
no Jensen gap because discrete balancing moves incidence toward the average.

It remains to compare `(L)` and `(U)`.  Use the worst allowed values independently:

```text
d <= h/8-1,
z_ell-d <= 5h/8-5/2.
```

After multiplying the desired strict inequality by `6` and dividing by the positive `N`, the
lower bound minus the upper bound is at least

```text
Q_h(N) = A_h N^2 - (19h/8 + 1 + 3/(2h)) N + 3h - 1,

A_h = h/8 + 7/4 + 3/(4h) + 1/(4h^2).
```

For `h>=8`, `Q_h` is increasing on `N>=2h+1`: already

```text
2 A_h (2h+1) > 19h/8 + 1 + 3/(2h).
```

At the left endpoint, direct expansion gives

```text
8h^2 Q_h(2h+1)
  = 4h^5 + 22h^4 + 70h^3 + 6h^2 + 2h + 2 > 0.   (A)
```

Thus `(L)` is strictly larger than `(U)` for every `N>=2h+1`, contradicting `(M1)`.  Therefore
`N<=2h=n`.

## 9. Sharpness and red-team audit

### The `c=0` packing is admitted with equality

Take a set `S` of `h` coordinates, put `(u0,u1)=(X,1)` on `S` and `(0,0)` off `S`.
The `h` kill scalars use the zero polynomial and the core `S^c`; the `h` align scalars use
`X+gamma` and the core `S`.  There are exactly `2h=n` scalars at agreement `h+1`.

The proof does not accidentally rule it out.  Its selected points lie on two affine lines, each
with core `h` and `h` points.  Section 6 concludes only `N<=2h` in this branch, with equality.

### Three-core attempted counterexamples collapse

Three half-sized cores can fit in `2h` coordinates only by using large pair overlaps.  Polynomial
compatibility on the overlaps is a univariate spline/syzygy constraint.  Even when this constraint
has two independent coefficient solutions, the deviations often form polynomial multiples of one
primitive syzygy.  If the intercept differences are `A(X)v` and direction differences are
`R(X)v`, every external scalar is

```text
gamma = -A(alpha_i)/R(alpha_i),
```

independent of which core is used, so it charges to a coordinate and yields at most `n` scalars.
An explicit stress test over `F_101` used disjoint four-root locators

```text
f_A = [75,67,27,98,1],
f_B = [30,100,72,74,1],
f_C = [ 2,33,100,86,1]       (coefficients low to high),
f_A + f_B - 2 f_C = 0.
```

Taking the direction syzygy to be `X` times the intercept syzygy makes all cross-core scalars
`-1/alpha_i`: still one per coordinate.  This experiment motivated the line-core proof but is not
an assumption of it.

### Degenerate cases checked

* **Vertical lines:** impossible for a line containing two selected points, because selected
  scalars are distinct.
* **Repeated witness polynomials:** harmless; the lifted points remain distinct in their scalar
  coordinate.
* **Agreement larger than `t`:** full agreement sets are used throughout; every inequality only
  improves.
* **Core `z>=t`:** nonjointness supplies the essential one fresh coordinate, giving the `max(1,...)`
  in `(L2)`.
* **Characteristic two:** no division by `2` occurs in the geometric proof.  Only inverses of
  nonzero scalar differences are used.
* **Small `h`:** `1<=k` and `16k<=2h` force `h>=8`.
* **Choosing one codeword among several:** arbitrary choice is valid; all arguments concern the
  resulting selected rich points, and hence bound every such selection and in particular the
  number of bad scalars.

## 10. Consequence for the field-normalized prize branch

Suppose `Q=2^128`, the field/order hypotheses needed for the `c=0` overlap packing hold, and
`floor(p/Q)=n`.  At rate `k/n=1/16`:

* the packing supplies `n+2` bad scalars at radius `1/2`, so the operational threshold is at most
  `1/2`;
* this theorem supplies at most `n` bad scalars at the predecessor radius `1/2-1/n`, hence
  `epsMCA <= n/p <= 1/Q` there;
* lattice constancy fills every real radius below `1/2`.

Consequently the operational threshold is exactly

```text
mcaDeltaStar(RS,1/Q) = 1/2
```

on this branch, once the already-separated arithmetic field/order certificate and the standard
threshold-ledger/lattice bridges are instantiated.

## 11. Scope and next target

This closes the matching half-predecessor good side at rate `1/16`, not at rates `1/8` or `1/4`.
At `k=n/8`, the inequality `8d<=h-8` is replaced by `4d<=h-4`; avoiding the two-line collapse
then permits rich lines of order `h/5`, and their collinear-triple correction is of the same leading
order as the third-moment margin.  A stronger weighted line-core/syzygy argument is needed there.

The reusable route is:

1. formalize the abstract rich-point incidence theorem above;
2. wire RS event witnesses to its hypotheses;
3. compose with the packing bad side and lattice threshold bridge;
4. attack `1/8` by replacing the crude collinear-triple count with a coordinate-charging theorem
   for compatible core syzygies.

