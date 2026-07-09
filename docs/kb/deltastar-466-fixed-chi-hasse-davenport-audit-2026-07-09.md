# Fixed-`chi` Hasse--Davenport audit for the Jacobi tower (2026-07-09)

**Verdict: exact structure, but no convolution contraction.**  The coefficient sequence

```text
J_j = J(lambda_j, chi)
```

is a genuine Gauss-ratio coboundary.  When `chi` belongs to the quotient-character family this
coboundary telescopes around translation orbits; when it does not, it links two distinct character
cosets.  In both cases Hasse--Davenport fixes products/phases but permits triple-convolution energy
at the full triangle-inequality scale.  The route is therefore an exact explanation of arithmetic
correlation, not a proof of `TripleConvEnergyBound` or `IterConvEnergyWick`.

This note uses the notation of
`Frontier/_R19JacobiFourierExpansion.lean`--`_R27FullTowerCollapse.lean`.  Let

```text
|F| = q,   |F*| = q - 1 = n m,
Lambda = <lambda> = {lambda_j : j in Z/m},
g(A) = sum_x A(x) psi(x),
J_j = J(lambda_j, chi).
```

The additive character `psi` is primitive.  All displayed identities use the convention that a
multiplicative character is zero at zero.

## 1. The universal Gauss-ratio identity

Whenever `lambda_j chi` is nontrivial, Mathlib's `jacobiSum_mul_nontrivial` gives

```text
J_j g(lambda_j chi) = g(lambda_j) g(chi).                     (1)
```

This is also proved in the function-valued interface as `R45GaussRatio.gauss_ratio`.  Thus the
normalized Jacobi phase is a quotient of two Gauss phases.  The important issue is whether the
denominator lives in the same `Lambda`-coset as the numerator.

## 2. Case I: `chi` is outside `Lambda`

Put

```text
a_j = g(lambda_j),       b_j = g(chi lambda_j).
```

The two arrays lie on distinct character cosets and no denominator in (1) is trivial.  Hence

```text
J_j = g(chi) a_j / b_j.                                      (2)
```

There is no internal translation telescope.  The Davenport--Hasse product formula supplies only
the global determinant

```text
prod_j b_j
  = -g(chi^m) chi(m^(-m)) prod_j a_j,

prod_j J_j
  = -g(chi)^m / (g(chi^m) chi(m^(-m))).                       (3)
```

Here `chi^m` is automatically nontrivial: in the cyclic character group of order `nm`,
`chi^m = 1` would imply `chi in Lambda`.  Formula (3) fixes one total phase and its norm is the
already-known tautology `q^((m-1)/2)` (because `J_0 = -1` and all `J_j`, `j != 0`, have norm
`sqrt(q)`).  It supplies no local additive-index smoothness.

## 3. Case II: `chi = lambda_h` lies in `Lambda`

Let `d = ord(h)` in `Z/m`.  Translation by `h` decomposes `Z/m` into `m/d` cycles.  On every cycle
not containing the trivial character, (1) telescopes exactly:

```text
prod_{j in C} J_j = g(chi)^d.                                 (4)
```

There is one exceptional cycle, `<h>`, containing both `j = 0` and `j = -h`.  At `j = -h` the
product character is trivial and the Gauss-ratio formula has its familiar factor-`q` defect.
Using

```text
J(1, chi) = -1,
J(chi^(-1), chi) = -chi^(-1)(-1),
```

together with Mathlib's `gaussSum_pow_eq_prod_jacobiSum`, the exact exceptional product is

```text
prod_{j in <h>} J_j = g(chi)^d / q.                            (5)
```

Consequently the whole-family product is

```text
prod_{j in Z/m} J_j = g(chi)^m / q.                            (6)
```

Direct complex-arithmetic probes over `(p,n,m) = (97,8,12)` for all `h = 1,...,6`, and over
`(193,16,12)` for `h = 1,5`, verified (4)--(6) to relative error below `8e-12`.

## 4. Quadratic specialization: an exact antipodal product, not a saving

If `chi` is nontrivial quadratic and belongs to `Lambda`, then `m` is even and
`h = m/2`.  Every generic translation orbit is a pair.  For
`alpha != 1` and `alpha chi != 1`,

```text
J(alpha, chi) J(alpha chi, chi)
  = g(chi)^2
  = chi(-1) q.                                                 (7)
```

The exceptional pair has product only `chi(-1)`, exactly a factor `q` smaller.  Identity (7) is
now machine-checked in
`Frontier/_JacobiFixedChiCoboundaryAudit.lean` as
`jacobi_antipodal_product_eq_gauss_sq` and
`jacobi_antipodal_product_eq_char_card`; `norm_jacobi_antipodal_product_eq_card` proves the
no-contraction norm statement itself.  The axiom audit contains only the accepted foundational
axioms.

The direction of (7) is important: a generic paired product has modulus `q`.  Pairing preserves
the full `sqrt(q)` modulus of each coefficient.  It does not contract it.

## 5. Quadratic duplication gives a nonlinear doubling coboundary

For every nontrivial quadratic `chi`, Davenport--Hasse duplication says

```text
g(A) g(A chi) = A(4)^(-1) g(A^2) g(chi).                      (8)
```

Combining (8) with (1), at every nondegenerate index,

```text
J_j = lambda_j(4) g(lambda_j)^2 / g(lambda_{2j}).              (9)
```

This precisely sharpens the round-28 observation

```text
g(lambda_j) g(lambda_{j+m/2})
  = lambda_j(4)^(-1) g(lambda_{2j}) g(lambda_{m/2})
```

from the inside-`Lambda` case.

The parity split is exact:

- if `m` is odd, the quadratic character is outside `Lambda`; doubling is a permutation of
  `Z/m`, and (9) has no exceptional nonzero index;
- if `m` is even, the quadratic character is `lambda_(m/2)`; (9) holds except at
  `j = m/2`, where its right side is `q` times the true degenerate Jacobi coefficient.

Thus the quadratic Jacobi phases are a *nonlinear doubling coboundary* of the quotient Gauss
phases.  This is an exact reduction to the Gauss-phase wall, not an independent source of
cancellation.

## 6. Explicit adversarial models at the convolution-energy scale

This section records exactly which identities each countermodel satisfies.  It does **not** claim
that either abstract phase model is realized by a finite field, nor that one model satisfies every
Hasse--Davenport relation simultaneously.  Its role is logical: the indicated identity package for
each model, even together with the correct exceptional magnitudes, does not imply the R23 Wick
bound.

### 6.1 All translation-coboundary and orbit-product laws, including the exceptional orbit

Take `m` even, `h = m/2`, and `epsilon in {+1,-1}`.  Choose `z in C` with

```text
z^2 = epsilon q,       |z|^2 = q,
```

and define a full coefficient sequence by

```text
J_0 = -1,
J_h = -epsilon,
J_j = z                for j notin {0,h}.                     (10)
```

This model has the exact Jacobi magnitude pattern: the two exceptional coefficients have norm
`1`, every generic coefficient has norm `sqrt(q)`.  It satisfies:

```text
J_j J_(j+h) = epsilon q       on every generic pair,
J_0 J_h     = epsilon,        on the exceptional pair,
prod_j J_j  = z^m / q.
```

Thus it satisfies (4)--(7), including the factor-`q` exceptional defect and the whole-family
product.  It also admits the full nondegenerate Gauss-ratio coboundary (1): set the special Gauss
values `a_0 = -1`, `a_h = g(chi)`, and on each generic pair choose any `a_j` of norm `sqrt(q)` and
put

```text
a_(j+h) = a_j g(chi) / z.
```

Then `J_j a_(j+h) = a_j g(chi)` for every index where (1) is supposed to hold; the reverse
equation follows from `z^2 = g(chi)^2 = epsilon q`.  The only omitted equation is the genuinely
invalid singular Gauss-ratio equation at `j=h`, where `lambda_h chi=1`.

Now mask the zero coefficient exactly as R21--R27 do:

```text
A_0 = 0,       A_j = J_j for j != 0.
```

Let `U_0=0`, `U_j=1` for `j!=0`, and put `r=-epsilon-z`.  Then

```text
A = z U + r delta_h.
```

The elementary counts

```text
U^(*2)(0) = m-1,                 U^(*2)(d) = m-2       (d != 0),
U^(*3)(0) = m^2-3m+2,           U^(*3)(d) = m^2-3m+3 (d != 0)
```

give the **exact** triple convolution.  With `B=A^(*3)`:

```text
B_0 = z^3 (m^2-3m+2) + 3 z^2 r (m-2),

B_h = z^3 (m^2-3m+3) + 3 z^2 r (m-1) + 3 z r^2 + r^3,

B_d = z^3 (m^2-3m+3) + 3 z^2 r (m-2) + 3 z r^2
      for d notin {0,h}.                                      (11)
```

Therefore

```text
E3 = |B_0|^2 + |B_h|^2 + (m-2)|B_d|^2.                        (12)
```

This is a reusable exact no-go, not just an asymptotic example.  Since
`|r/z| <= 1+1/sqrt(q) <= 2`, for every even `m>=10`, reverse triangle inequality in the last line
of (11) yields

```text
|B_d| >= q^(3/2) (m^2-9m+3),

E3 / (6 m^3 q^3)
  >= (m-2)(m^2-9m+3)^2 / (6m^3)
   = (1+o(1)) m^2/6.                                         (13)
```

So the exact magnitudes, every valid fixed-`chi` Gauss-ratio equation, every translation-orbit
product, the exceptional factor-`q` defect, and the global product law are jointly compatible with
the full `m^5 q^3` triangle-inequality energy.  They cannot imply an absolute-constant
`TripleConvEnergyBound`.

### 6.2 The local quadratic duplication law by itself

The doubling identity (9) has an even simpler saturation model in the outside-family (`m` odd)
case.  Set every abstract normalized quotient Gauss phase to `1`.  For every nonzero `j`, doubling
does not hit zero, and (9) gives

```text
A_j = sqrt(q) lambda_j(4),       A_0=0.                        (14)
```

Thus (14) satisfies the exact local duplication-coboundary formula (9) and the exact generic
magnitudes.  Since `j |-> lambda_j(4)` is a linear character, every summand in a fixed convolution
fiber has the common phase `lambda_d(4)`.  Hence its energy is exactly

```text
E3 = q^3 [ (m^2-3m+2)^2
          + (m-1)(m^2-3m+3)^2 ]
   = (1+o(1))m^5q^3.                                          (15)
```

This second model is asserted only against the local duplication law (9), not against the global
determinant (3).  Together, (13) and (15) locate the failure precisely: neither the complete
translation-coboundary product package nor the local doubling-coboundary package controls additive
convolution energy.

## 7. Numerical refutation of an inside/outside energy dichotomy

Direct prime-field probes of the actual quadratic Jacobi sequence used the exact R22
nonzero-index triple convolution.  The table reports

```text
E3 / (6 m^3 p^3).
```

| `(p,n,m)` | quadratic `chi` | ratio |
|---|---:|---:|
| `(433,8,54)` | inside `Lambda` | `3.8601` |
| `(929,8,116)` | inside `Lambda` | `2.7488` |
| `(457,8,57)` | outside `Lambda` | `2.7213` |
| `(937,8,117)` | outside `Lambda` | `2.1396` |

Both parity branches remain at comparable arithmetic constant multiples of the Wick scale; neither
branch exhibits a structural vanishing or a new power saving.  These values are diagnostics, not
proofs.

## 8. Consequence for the live route

The exact information supplied by Gauss--Jacobi and Hasse--Davenport is now separated cleanly:

1. **magnitudes:** already exact (`1` at degenerate indices, `sqrt(q)` elsewhere);
2. **translation/doubling products:** (3)--(9), exact but multiplicative;
3. **needed prize input:** additive-index cancellation in `J^{*r}` at `r = 3` and ultimately
   `r about log q`.

Passing from item 2 (product identities) to item 3 (additive convolution cancellation) is precisely
the missing analytic step.  Neither the complete translation-orbit package nor the local quadratic
duplication package alone controls additive convolution energy; the corresponding aligned models
above refute those two implications at the correct `m^5 q^3` scale.  A successful continuation must
use joint arithmetic information that excludes those aligned Gauss-phase configurations--for example
a quantitative signed equidistribution theorem strong enough on the sparse quotient-character
grid--rather than another isolated product identity.

## References and in-tree anchors

- `Mathlib.NumberTheory.JacobiSum.Basic`: `jacobiSum_mul_nontrivial`,
  `gaussSum_pow_eq_prod_jacobiSum`.
- `Mathlib.NumberTheory.GaussSum`: `gaussSum_sq`.
- `Frontier/_R45GaussRatio.lean`: function-valued Gauss-ratio identity.
- `Frontier/_R27FullTowerCollapse.lean`: the additive convolution-energy target.
- Rojas-Leon, *Equidistribution and independence of Gauss sums*, arXiv:2207.12439, for the
  broader statement that Hasse--Davenport relations are the algebraic relations that remain before
  quantitative equidistribution.
