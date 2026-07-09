# R323 — constrained lag orthogonality returns the sixth moment (2026-07-09)

**Status: REFUTED.**  The proposed `p >= n^4` closure obtained by summing the R289
lag hyperplane first drops one factor of `y2`.  With the correct character monomial, the
lag sum collapses exactly to the original sixth moment.  It therefore recovers the known
`p >= n^6` tuplewise-Weil barrier rather than improving it.

This note concerns the concrete R37/R289 normal form, not the abstract consumer sockets:

- `Frontier/_R37SexticExact.lean`;
- `Frontier/_R289ConstrainedSexticAverageSocket.lean`;
- `Frontier/_R290SignedConnectedSexticSocket.lean`;
- `Frontier/_R293CollisionBudgetReductionSocket.lean`.

## 1. Notation and the exact five-variable slice

Let `F = F_p`, let `G <= F*` have order `n`, and put

```text
m = (p - 1) / n,       H = Z/m,       Q = F*/G.
```

Let `lambda = lambda_1` generate the quotient-character family, so that
`ker(lambda) = G` and `lambda_j(z) = lambda(z)^j`.  Put

```text
f(z) = chi(1 - z),
A_{a,b} = (f lambda_0) *_x (f lambda_a) *_x (f lambda_b),
```

where `*_x` is multiplicative convolution.  The R37 slice is

```text
S_u(a,b,a',b',t)
  = sum_w A_{a,b}(u w) conjugate(A_{a',b'}(w)) lambda_t(w),    u in G.
```

Expanding the two triple convolutions with variables `x1,x2,y1,y2,w in F*`
gives the six arguments

```text
x3 = u w / (x1 x2),       y3 = w / (y1 y2).
```

The `lambda` factor is exactly

```text
lambda(u^b x1^(-b) x2^(a-b) y1^(b') y2^(b'-a') w^(b-b'+t)).       (1)
```

The remaining factor is

```text
f(x1) f(x2) f(x3) conjugate(f(y1) f(y2) f(y3)).                   (2)
```

The factor `u^b` in (1) is harmless because `u in G`, but retaining it makes the
orthogonality calculation auditable.

## 2. Summing the cubic lag hyperplane

Let

```text
L = {(a,b,a',b',t) in H^5 : 3t + a + b = a' + b'}.
```

Eliminate `a' = 3t + a + b - b'` in (1).  The four free character sums over
`a,b,b',t` impose

```text
x2 / y2                  in G,
u w / (x1 x2 y2)         in G,
y1 y2^2 / w              in G,
w / y2^3                 in G.                                  (3)
```

The square on `y2` in the third line is essential.  One factor comes from
`conjugate(lambda_{b'}(y3))`; the other comes from substituting `a'` into
`lambda_{a'}(y2)^{-1}`.

Equivalently, in additive notation in `Q`, the coefficient vector of
`(a,b,a',b',t)` is

```text
([x2], [u]+[w]-[x1]-[x2], -[y2], [y1]+[y2]-[w], [w]).
```

It must be a multiple of `(1,1,-1,-1,3)`, the normal to the lag hyperplane.
Since `[u]=0`, this gives

```text
[x1] = [x2] = [y1] = [y2] = c,       [w] = 3c.                  (4)
```

Thus (3), not the erroneous condition `y1 y2 / w in G`, is also confirmed by a
coordinate-free linear-algebra check.

## 3. The factorization and boxed identity

Choose one representative `r` of `c in Q` and write

```text
x1 = r g1,   x2 = r g2,   y1 = r h1,   y2 = r h2,   w = r^3 k,
```

with `g1,g2,h1,h2,k in G`.  Then

```text
x3 = r (u k / (g1 g2)),       y3 = r (k / (h1 h2)).
```

The change of variables

```text
k = h1 h2 h3,       u = g1 g2 g3 / (h1 h2 h3)
```

is a bijection between `(g1,g2,h1,h2,k,u) in G^6` and
`(g1,g2,g3,h1,h2,h3) in G^6`.  Hence (2) factorizes.  Define the coset sum

```text
T_chi(c) = sum_{g in G} chi(1 - r g),
```

which is independent of the representative `r`.  Four applications of character
orthogonality now give the exact identity

```text
┌──────────────────────────────────────────────────────────────────────────────┐
│ sum_{(a,b,a',b',t) in L} sum_{u in G} S_u(a,b,a',b',t)                      │
│     = m^4 sum_{c in F*/G} |T_chi(c)|^6.                                     │
└──────────────────────────────────────────────────────────────────────────────┘   (5)
```

R37 contributes one further factor `m`.  Therefore the full constrained six-Jacobi
sum is

```text
m^5 sum_c |T_chi(c)|^6,
```

which is the original sixth-moment object in quotient coordinates.  The interchange is
an exact involution of the normal form, not a new low-dimensional point count.

## 4. The fully-distinct restriction does not remove the resonance

For a lag tuple define its six offsets

```text
O(a,b,a',b',t) = {t, t+a, t+b, 0, a', b'}.
```

Let `L_dist` be the subset of `L` on which these six elements are pairwise distinct.
The hyperplane `L` has `m^4` elements.  Each of the 15 pair-equality conditions cuts
out exactly `m^3` elements: every resulting linear equation has at least one unit
coefficient.  Consequently

```text
m^4 - 15 m^3 <= |L_dist| <= m^4.                              (6)
```

On the resonance (4), the phase (1) is `1` for every lag in `L`, because its exponent
is a multiple of `3t+a+b-a'-b'`.  Restricting to `L_dist` therefore changes the
resonance coefficient from `m^4` to `|L_dist|`; by (6), it remains full strength.

More explicitly, inclusion-exclusion over the 15 equality hyperplanes gives a Fourier
kernel of the form

```text
K_dist = m^4 1_{R0} + sum_{nontrivial collision partitions pi}
           mu(pi) m^{d(pi)} 1_{R_pi},       d(pi) <= 3,          (7)
```

where `R0` is (4).  The other `R_pi` are the repeated-index resonance varieties.
They are precisely the correction strata isolated by R291--R295.  Formula (7) explains
why the generic-distinct term is signed, but it does not cancel `R0` identically.

No separate Lean file is added here.  The current R289/R291 sockets do not yet define
the concrete six-offset `L_dist` finset, so formalizing only (6) would first require a new
parallel interface.  The union bound is elementary once that concrete object exists.

## 5. Tuplewise Weil recovers exactly beta = 6

Put

```text
M6 = sum_{c in F*/G} |T_chi(c)|^6
   = (1/n) sum_{r in F*} |sum_{g in G} chi(1-rg)|^6.
```

Expanding gives

```text
M6 = (1/n) sum_{g_1,g_2,g_3,h_1,h_2,h_3 in G}
       sum_{r in F*} chi(prod_i(1-rg_i) / prod_i(1-rh_i)).       (8)
```

For a character of order `d >= 2`, the rational function in (8) is a `d`-th power only
when the root-multiplicity differences are `0 mod d`.  There are `O(n^3)` such tuples:

- for `d >= 4`, the two triples have the same multiset;
- for `d = 3`, one additionally has the all-equal triple patterns;
- for `d = 2`, equality of parity supports gives either a common three-element support
  or a common one-element support, still only `O(n^3)` ordered pairs.

The exceptional tuples contribute `O(p n^2)` after the factor `1/n`.  Weil gives
`O(sqrt(p))` for each of the remaining `O(n^6)` tuples, hence

```text
M6 << p n^2 + n^5 sqrt(p).                                    (9)
```

The desired Wick scale is

```text
M6 << m n^3 = (p-1)n^2.
```

The second term in (9) fits this scale exactly when

```text
n^3 <= sqrt(p),       equivalently p >= n^6.                   (10)
```

At the operational exponent `p = n^beta`, `beta ~= 5.27`, tuplewise Weil loses

```text
n^(3-beta/2) ~= n^0.365,
```

about `2^11` when `n = 2^30`.  Thus (5) decisively refutes the apparent `p >= n^4`
closure and recovers the existing beta-six wall with no hidden slack.

## 6. Why Katz--Laumon stratification does not repair (5)

The closest general primary source is Bonolis--Kowalski--Woo,
[Stratification theorems for exponential sums in families](https://arxiv.org/abs/2506.18299),
arXiv:2506.18299v3.

- Their Theorem 1.3 (Fouvry--Katz) stratifies an **additive twist parameter**
  `h in F_p^N`.  Outside a codimension-`j` locus it bounds a fixed `d`-dimensional
  sum by `C p^(d/2+(j-1)/2)`.
- Theorem 1.3 is uniform in the multiplicative character and, by Remark 1.5, can use
  one datum for all invertible functions `g`.
- Theorems 1.6 and 1.8 make the geometry algebraically uniform in finite-type fiber
  families.  Theorem 1.14 is the trace-function version for a global semiperverse,
  fiberwise-transverse object.  Example 1.13(1) verifies those properties for shifted
  Kummer sheaves.  Theorem 1.16 gives analytic uniformity for bounded-degree varieties
  in the additive-twist setting.

Growing Kummer order is not itself the obstruction.  Fouvry--Kowalski--Michel--Sawin,
[Lectures on Applied l-adic Cohomology](https://arxiv.org/abs/1712.03173),
arXiv:1712.03173v3, Section 4.2.2, records that every nontrivial Kummer sheaf has rank
one, Swan conductor zero at `0,infinity`, and conductor exactly `3`, independent of its
order.  In (1), varying the lags changes tame local monodromy but not the six-component
divisor support.

The decisive mismatches are instead:

1. R289's parameters live in a subgroup of the **character group** and change the local
   system; they are not BKW's additive Fourier parameter `h`.
2. Here the additive phase is `f+h.x = 0`.  For the common Theorem 1.3 datum, `h=0`
   must lie in the deepest exceptional locus (take the trivial multiplicative summand,
   whose untwisted sum is `#V`).  The theorem is silent at precisely this point.
3. Encoding all character lags as `mu_m` produces a parameter scheme of degree `m`, not
   a bounded-complexity family.  Uniform pointwise conductor bounds do not imply signed
   cancellation when summing over these changing sheaves.
4. Even granting the optimal individual five-variable estimate `|S_u| << p^(5/2)`,
   triangle inequality over about `m^4 n` lag--`u` pairs, followed by R37's factor `m`,
   gives `m^4 p^(7/2)`.  This exceeds `m^3 p^3` by `m sqrt(p)`.

The missing result is therefore a Mellin/Kummer **signed family** theorem at torsion level
`m`, not another pointwise Katz--Laumon stratification.

## 7. Numerical probes (not proofs)

Direct complex-arithmetic checks used a primitive generator, the quotient characters
described above, and quadratic `chi`.

| `(p,n,m)` | `|L|` | left side of (5) | right side of (5) | discrepancy |
|---|---:|---:|---:|---:|
| `(17,4,4)` | `256` | `33024` | `33024` | `< 3e-13` |
| `(29,4,7)` | `2401` | `10144225` | `10144225` | `< 7e-8` |

For `(29,4,7)`, `|L_dist| = 72` and the signed distinct inner sum was `-81432`, namely
`-0.06814045 m^2 p^3`.  This last value illustrates the R290 warning: collision-partition
Fourier terms can cancel the positive `R0` contribution, so (5)--(7) are a no-go for the
purported shortcut, not a positivity refutation of the desired bound.

## 8. Post-audit: character-variety stratification still does not close the sum

Two primary sources address character-indexed families more directly than BKW.  They
clarify the right geometric language, but their stated quantitative conclusions do not
supply the two powers of `m` required by R293.

### 8.1 Zurbuchen: the correct parameter space, but no sparse signed estimate

Zurbuchen,
[Equidistribution for Tannakian monodromy groups](https://arxiv.org/abs/2602.21878),
arXiv:2602.21878v1, genuinely includes a character parameter.

- Theorem 3.24 proves uniform lissity over the scheme parameter for all characters of a
  semiabelian variety.
- Theorem 3.32 stratifies both a finite-type scheme `X` and the character variety of
  `G = S x U`; away from codimension-`i` and codimension-`j` strata it gives
  `sum_t rho(t)t_K(t,x) <<_K |k|^((i+j)/2)` after the paper's perverse/weight
  normalization.
- Proposition 2.84 shows that a thin character subset of codimension `d` has density
  `O_Delta(|k|^(-d))` among extension-field arithmetic characters.
- Theorems 7.17 and 7.18 give Tannakian equidistribution outside a proper thin subset as
  the extension degree tends to infinity.

The R37 five-variable sum fits the input language: take the summation group
`S = G_m^5`, the scheme parameter `X = G_m` with coordinate `u`, and the fixed Kummer
trace function given by (2).  The lag character has exponent vector

```text
e = (-b, a-b, b', b'-a', b-b'+t).
```

On `3t+a+b=a'+b'`, these vectors satisfy

```text
e1 + e2 + e3 + e4 + 3e5 = 0.                                 (11)
```

Thus the entire constrained family lies in one codimension-one algebraic cotorus of the
five-dimensional character variety.  Pairwise distinctness only deletes hyperplanes inside
this cotorus.  Formula (5) is the corresponding surviving resonance, so Theorem 3.32 does
not certify that this cotorus avoids its first thin exceptional locus.

There are two further quantitative mismatches:

1. The sampled characters are not all arithmetic characters of `G_m^4(F_p)`: each
   coordinate lies in `H`, the image of the `n`-th-power map on the full character group.
   Geometrically this uses the degree-`n` isogeny `[n]`.  Zurbuchen's constants are
   written `<<_K` (and Proposition 2.84 uses `<<_Delta`); no dependence on a growing
   isogeny degree is stated.
2. Theorems 7.17--7.18 are qualitative limits over all characters as the extension degree
   tends to infinity.  They do not give a power-saving rate for the sparse fixed-field grid
   `H^4`, nor signed cancellation over that grid.

So this paper repairs the *categorical formulation* of the BKW mismatch, but does not
imply the R293 bound.

### 8.2 Rojas-Leon: explicit complexity shows the quantitative gap

Rojas-Leon,
[Equidistribution and independence of Gauss sums](https://arxiv.org/abs/2207.12439),
arXiv:2207.12439v3, gives an explicit version that can be stress-tested.
In Section 5, Lemma 2 bounds the complexity of a Gauss-sum object with exponent vector
`a` by `2 max_i |a_i|`.  Theorem 4 then bounds a normalized Fourier coefficient by

```text
C(r) N(r)^(||c||_1-1) A^(||c||_1) p^(-1/2) + O(n_coord A/p),    (12)
```

up to the displayed denominator tending to one.  Here `A` bounds the exponent vectors,
`n_coord` is the number of Gauss-sum coordinates, and `c` is the tested torus Fourier
mode.

For the direct six-Jacobi product, use five independent character variables (six indices
subject to one sum relation).  Each normalized Jacobi sum is a ratio of two normalized
Gauss sums.  The product of three Jacobi sums and three conjugates therefore has

```text
r = 5,       n_coord = 12,       ||c||_1 = 12.
```

There are two standard ways to restrict the five variables to `H`.

**Power-map parameterization.**  Write every `H`-character as `theta^n`, with `theta`
ranging over the full character group.  This map is `n^5`-to-one, so normalized averages
agree exactly, but the linear-form exponents are multiplied by `n`.  Since the lag forms
have coefficients at most `3`, (12) has the optimistic size

```text
O(n^12 / sqrt(p)) + O(n/p).                                   (13)
```

Thus even mere equidistribution from this estimate asks for `p >> n^24`.

**Subgroup-indicator parameterization.**  For one character variable,

```text
1_H(alpha) = (1/n) sum_{g in G} alpha(g).
```

After normalizing by `|H|`, the factor `1/n` is absorbed by
`|H| n = p-1`; what remains is a sum, not an average, over `g in G`.  Five independent
variables therefore lose `n^5`.  Applying the full-character estimate uniformly to the
twists gives

```text
O(n^5 / sqrt(p)),                                              (14)
```

so mere equidistribution asks for `p >> n^10`.  This verifies the five-indicator count.

Neither exponent is close to sufficient for R293.  After dividing the six-Jacobi product
by `p^3`, the generic constrained sum contains about `m^5` unit phases, while the target
is `O(m^3)`.  It needs a normalized Fourier coefficient of size `O(m^(-2))`, not merely
`o(1)`.  Comparing (13) or (14) with `m^(-2) = (n/(p-1))^2` shows that the stated
`p^(-1/2)` error cannot reach the prize scale for any prize-like regime `p >> n`:

```text
n^5 p^(-1/2) <= m^(-2)
    would imply n^3 p^(3/2) <= 1.                              (15)
```

The power-map route is still weaker.  Moreover, the independence hypothesis of
Rojas-Leon's Theorem 1 must be checked against the proportional exponent vectors; failure
would only remove the estimate, not improve it.  Consequently `beta > 10` and
`beta > 24` are thresholds for *qualitative equidistribution by these two implementations*,
not closures of the DC-subtracted Wick-scale sextic bound.
