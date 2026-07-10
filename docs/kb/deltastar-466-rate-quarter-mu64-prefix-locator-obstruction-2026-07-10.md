# Rate-quarter `mu_64` prefix-locator obstruction (2026-07-10)

## Verdict

The most structured degree-fifteen route at `mu_64` is blocked at the actual
prize prime.

Let a prefix endpoint be a disjoint union of dyadic exponent cosets of sizes

```text
8 + 4 + 2 + 1 = 15.
```

An exact fixed-field census proves executably:

> There is no pairwise-disjoint affine locator triangle over `F_P1` having
> two `8+4+2+1` prefix endpoints.  The third degree-fifteen locator was
> allowed to be an arbitrary fifteen-subset of `mu_64`.

The census uses only exponent translations, which are honest symmetries in a
fixed prime field.  It enumerates

```text
prefix endpoints                         145,600
translation classes                       2,275
disjoint structured endpoint pairs   55,301,400
P1 affine-locator hits                         0
```

An independent small-prime implementation gives zero already over `F_193`
after universal affine/Galois normalization:

```text
affine/Galois classes                        247
disjoint structured endpoint pairs    6,174,000
F193 hits                                      0
F257/F449 survivors                            0
```

Thus both the universal and characteristic-specific P1 versions of the
minimal prefix shape are ruled out by exact executable censuses.  This is not
yet a kernel-checked finite census.

One additional five-node prefix shape was exhausted on the universal side:

```text
shape                                  4+4+4+2+1
prefix endpoints                           728,000
affine/Galois classes                        1,105
disjoint structured endpoint pairs    117,255,600
F193 hits / three-prime survivors                0 / 0
```

Again, the third locator was arbitrary.  This last result obstructs universal
identities; it does not obstruct identities occurring only at P1.

## 1. Prefix cosets and their sparse locators

For `s` dividing `64`, put

```text
C_s(r) = {r + (64/s)j mod 64 : 0 <= j < s}.
```

If `zeta` is a primitive sixty-fourth root, the locator of this coset is

```text
product_{e in C_s(r)} (X-zeta^e) = X^s-zeta^(sr).
```

Consequently an `8+4+2+1` endpoint has locator

```text
P(X) = (X^8-a8)(X^4-a4)(X^2-a2)(X-a1).
```

There are exactly

```text
8 * 14 * 26 * 50 = 145,600
```

disjoint choices.  The four degrees have unique subset sums, so every
non-leading coefficient is one signed monomial in the four parameters.

## 2. Why the search allows an arbitrary third locator

Fix disjoint endpoint sets `A,C` and evaluate their monic locators on a root
`x` outside both.  A monic affine member

```text
P_B = lambda P_A + (1-lambda) P_C
```

vanishes at `x` precisely when

```text
P_A(x) / P_C(x) = (lambda-1)/lambda.
```

Therefore a fifteen-fold collision of the exact ratio

```text
R(x) = P_A(x)/P_C(x)
```

among the remaining thirty-four roots produces an arbitrary disjoint
fifteen-root locator `B`.  Conversely, every disjoint affine triangle gives
such a collision.  Since the affine member is monic of degree fifteen, a
ratio bucket cannot contain more than fifteen roots unless the two endpoints
are equal.

The probes enumerate structured `A,C` but place no structural condition on
the collision bucket `B`.  This is strictly stronger than checking triples
inside the prefix family.

## 3. Fixed-field symmetry audit

The two censuses intentionally have different orbit groups.

* Simultaneous translation `e -> e+s` is induced by scaling the polynomial
  variable.  It preserves affine locator relations over every field and is
  used by the P1 census.
* Odd multiplication `e -> ue` is the cyclotomic Galois action in
  characteristic zero.  It is legitimate for filtering universal identities,
  but it is not an automorphism of a fixed prime field.  It is used only by
  the small-prime universal census.

The P1 result does not infer a fixed-field obstruction from a
Galois-normalized small-prime search.  It performs the larger 2,275-class
fixed-field search directly.

## 4. Exact P1 arithmetic

The P1 probe computes in

```text
P1 = 365375409332725729550921208179070755120141565953
   = 2^158 + 192*2^30 + 1.
```

It uses an exact three-limb Montgomery implementation.  The implementation
checks:

* encoding, multiplication, and inversion on small constants;
* the decoded primitive sixty-fourth root against an independently computed
  integer constant;
* `omega^32=-1` and `omega^64=1`;
* every batch-inversion product identity.

Every structured locator evaluation is also computed through the independent
four-binomial formula, rather than by copying coefficient data from the
small-prime program.  Ratio keys retain all 158 field bits; hashing only
selects a table slot, and full field equality decides collisions.

## 5. Structural Segre obstruction

There is also a field-universal conceptual obstruction when all three
locators have the `8+4+2+1` form.

For two factor coordinates `i,j`, suppose an affine combination preserves
the singleton coordinates and their pair product.  Expanding the pair
coordinate gives

```text
lambda(1-lambda)(a_i-c_i)(a_j-c_j) = 0.
```

At a non-endpoint affine parameter, at least one endpoint coordinate must
therefore agree.  Applying this to every pair says the endpoints differ in at
most one of their four factors.  Hence they share at least three binomial
factors and cannot have disjoint root sets.

This algebra is axiom-clean in

```text
Frontier/_RateQuarterMu64PrefixSegreRigidity.lean
```

through

```text
affineSegre_two_coordinate_rigidity
affineSegre_changedCoordinates_card_le_one
not_affineSegre_of_two_changed_coordinates
```

The executable census is stronger because its third locator need not lie on
the Segre variety.

## 6. Norm route red team

A tempting replacement for the direct P1 census was to lift every ratio
collision to characteristic zero using a small evaluation determinant

```text
D(A,C;x,y) = P_A(x)P_C(y)-P_A(y)P_C(x).
```

For a cyclotomic power-basis squared norm budget `L`, the generic resultant
engine would give `|Norm(D)| <= L^16`.  The largest integral budget fitting
strictly below P1 is `L=939`:

```text
939^16 < P1 < 940^16.
```

This route is false at the required uniform constant.  A deterministic
million-sample exact group-ring red team found

```text
max sampled l2Sq = 16,608.
```

For the reported witness the actual resultant norm is

```text
30281508739224626556021456629699616759258224104901233986240512,
```

a 205-bit integer larger than P1.  Its factorization is

```text
2^51 * 257^2 * 167873^2 * 2687880090303167^2.
```

This does not exhibit P1 divisibility and does not weaken the direct census.
It only refutes the hoped-for one-line `l2Sq <= 939` norm proof.  The red-team
scan is randomized evidence, not an exhaustive theorem.

## 7. Reproduction

Universal and cross-prime census:

```bash
clang++ -O3 -std=c++17 -pthread -Wall -Wextra -Wpedantic \
  scripts/probes/probe_rate_quarter_mu64_prefix_locator_orbits.cpp \
  -o /tmp/probe_mu64_prefix
/tmp/probe_mu64_prefix 8 8421
/tmp/probe_mu64_prefix 8 44421
```

Direct fixed-field P1 census:

```bash
clang++ -O3 -std=c++17 -pthread -Wall -Wextra -Wpedantic \
  scripts/probes/probe_rate_quarter_mu64_prefix_locator_p1.cpp \
  -o /tmp/probe_mu64_prefix_p1
/tmp/probe_mu64_prefix_p1 8
```

Norm-budget falsifier:

```bash
clang++ -O3 -std=c++17 -Wall -Wextra -Wpedantic \
  scripts/probes/probe_rate_quarter_mu64_prefix_eval_minor.cpp \
  -o /tmp/probe_mu64_minor
/tmp/probe_mu64_minor 1000000
```

On the 2026-07-10 development machine, the minimal-prefix small-prime pass
takes under ten seconds, the five-node small-prime pass about one minute, and
the full P1 pass about ninety seconds with eight workers.

## 8. Remaining route

The census does **not** rule out:

* a degree-fifteen triangle with fewer than two `8+4+2+1` endpoints;
* a P1-specific triangle based on another five- or six-node prefix shape;
* an unstructured degree-fifteen triangle;
* a larger `mu_128` construction.

It does rule out the minimal binary-partition seed in the strongest natural
orientation: even granting an arbitrary third locator does not produce a P1
triangle.  The next honest finite-search targets are the other five-node
shapes `8+4+1+1+1`, `8+2+2+2+1`, and `4+4+4+2+1` at P1, or a genuinely
non-prefix parameterization.  Their fixed-field search spaces are much
larger, so a new invariant or a meet-in-the-middle direction index is likely
needed before exhaustive enumeration.
