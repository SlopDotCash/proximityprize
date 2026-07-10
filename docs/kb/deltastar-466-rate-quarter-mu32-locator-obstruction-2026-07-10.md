# Rate-quarter `mu_32` split-locator obstruction (2026-07-10)

## Verdict

The obvious next dyadic improvement of the three-line smooth construction is
blocked.

* The known `mu_16` cubic locator identity composes with `X^2` to degree `6`
  on `mu_32`.  An exact affine-orbit census finds no new non-antipodal
  three-prime degree-`6` survivor.
* For pairwise-disjoint degree-`7` locators on `mu_32`, the same
  Galois-normalized census checks `3,318,272,100` disjoint `(A,C)` pairs.
  There are `168` `F_97` hits among those normalized representatives and
  **zero** hits surviving `F_193` and `F_257`.
* A characteristic-zero cyclotomic identity would reduce at every split good
  prime.  Thus the two-stage exact census rules out a universal disjoint
  degree-`7` locator triangle on `mu_32`.  This conclusion depends on the
  executable exhaustive census; it is not yet a Lean-formalized finite census.
* Antipodal parity and a cyclotomic norm bound upgrade the result to the actual
  prize prime `P1`: every `P1`-vanishing `e_1`-anchored minor is too small in
  norm to be characteristic-specific, while disjoint odd-cardinality root
  sets always have distinct `e_1`.  Hence there is **no disjoint degree-`7`
  locator triangle on `mu_32` over `P1`**.
* A separate axiom-clean Lean theorem rules out every *nested* low-degree
  quotient extension of the old coprime locator line.  Such an extension is
  forced to use one common multiplier, so all appended roots are shared and
  contribute no new disjoint pair block.

The prize-field upgrade uses standard cyclotomic norm/Parseval reasoning, the
universal executable census, and an already-formalized antipodal collision
law; it is not yet one end-to-end Lean theorem.  It does not rule out a
non-nested construction at `mu_64` or above.

## Why degree seven matters

Let a smooth base cell have `B` fibres, let each of the three pairwise root
blocks have `d` fibres, and let every line core have `L` fibres.  The private
part of each core has size `L-2d`, hence the covered union has size

```text
U = 3d + 3(L-2d) = 3L-3d.
```

Covered fibres supply one safe bad scalar each and uncovered fibres supply
three, so the scalar ledger is

```text
U + 3(B-U) = 3B - 6L + 6d.
```

To exceed the field-normalized threshold `B`, one needs asymptotically
`L < B/3+d`.  Since the radius is `1-L/B`, the resulting upper-radius limit is

```text
delta < 2/3 - d/B.
```

The known ratios `3/16 = 6/32` give `23/48`.  A degree-`7` seed on `mu_32`
would improve this to `43/96`; ratios tending to `1/4` would reach `5/12`.

## Exhaustive universal-identity census

The probe is

```text
scripts/probes/probe_rate_quarter_mu32_locator_orbits.cpp
```

For a `d`-subset `S` of the exponent group `Z/32`, write

```text
P_S(X) = product_{e in S} (X-zeta^e).
```

For fixed disjoint `A,C`, a third root `x` belongs to a monic affine member
precisely when

```text
lambda(x) = P_C(x) / (P_C(x)-P_A(x))
```

takes the same value.  A collision of multiplicity `d` gives the candidate
root set `B`.  The program:

1. enumerates cyclotomic affine orbits of `C` under `e |-> u*e+s`, with `u`
   odd;
2. enumerates every `A` disjoint from that representative;
3. finds all `d`-fold ratio collisions over `F_97`;
4. rechecks every hit coefficient-by-coefficient over `F_193` and `F_257`.

All three primes are `1 mod 32`, so `mu_32` splits.  There is an important
scope distinction in the orbit reduction:

* translation `e |-> e+s` is a variable-scaling symmetry over every field;
* multiplication `e |-> u*e` is the cyclotomic Galois action
  `zeta |-> zeta^u` and is exact for characteristic-zero identities;
* it need not preserve an accidental identity inside one fixed prime field,
  whose field automorphism group is trivial.

Therefore the orbit census is exhaustive for the **universal/cyclotomic**
question, but `f97_hits` is not a full census of all characteristic-specific
`F_97` triples.  If a characteristic-zero identity existed, applying a Galois
automorphism and a translation would put its `C` set at one enumerated
representative.  Its coefficient minors would then vanish after reduction at
every split prime, so it would necessarily appear as a three-prime survivor.

Reproduction:

```bash
clang++ -O3 -std=c++17 -pthread -Wall -Wextra -Wpedantic \
  scripts/probes/probe_rate_quarter_mu32_locator_orbits.cpp \
  -o /tmp/probe_mu32_orbits
/tmp/probe_mu32_orbits 6 16
/tmp/probe_mu32_orbits 7 8
```

Final summaries:

```text
DONE degree=6 affine_orbits=1943 disjoint_pairs_tested=447336890
  f97_hits=2972 three_prime_hits=8 antipodal_three_prime_hits=8

DONE degree=7 affine_orbits=6903 disjoint_pairs_tested=3318272100
  f97_hits=168 three_prime_hits=0 antipodal_three_prime_hits=0
```

Here `f97_hits` means hits on the Galois-normalized representatives.  The eight
degree-`6` outputs count orientations.  Every root set is invariant
under exponent translation by `16`, hence is a polynomial in `X^2` and is a
dyadic lift of a `mu_16` cubic.  One displayed survivor is

```text
A={0,1,9,16,17,25}
B={7,8,15,23,24,31}
C={10,12,14,26,28,30}.
```

No non-antipodal universal degree-`6` candidate survives the normalized
three-reduction filter.  This statement does not classify all accidental
three-prime coincidences without Galois symmetry.

## Prize-field upgrade by a small anchored-minor norm

The universal census alone does not automatically rule out coincidences in a
single prime field, because odd exponent multiplication is not a prime-field
automorphism.  For the concrete prize prime, however, the relevant locator
minors are too small to vanish accidentally.

Write the degree-`7` locator coefficients using elementary symmetric sums
`e_j(S)`.  For difference vectors

```text
x_j = e_j(A)-e_j(C),   y_j = e_j(B)-e_j(C),
```

collinearity implies every minor

```text
Delta_{k,j} = x_k*y_j - x_j*y_k
```

vanishes modulo `P1`.  Take the anchor `k=1`.

For disjoint root sets, an `e_1` difference is a signed sum of fourteen
distinct `32`nd roots, so its group-ring coefficient vector has

```text
||x_k||_2^2, ||y_k||_2^2 <= 14.
```

Every elementary difference has `l1` norm at most

```text
2 * max_j choose(7,j) = 70.
```

Young's convolution inequality and the triangle inequality give

```text
||Delta_{k,j}||_2 <= 2 * 70 * sqrt(14),
||Delta_{k,j}||_2^2 <= 274400.
```

Parseval over all thirty-two characters bounds the mean square over the
sixteen odd Galois embeddings by twice this value.  AM--GM therefore gives

```text
|Norm(Delta_{k,j})| <= 548800^8
  = 8228351233069416798082784296960000000000000000
  < 365375409332725729550921208179070755120141565953
  = P1.
```

If `Delta_{k,j}` vanishes under the split reduction to `F_P1`, then `P1`
divides its algebraic norm.  The strict bound forces that norm, and hence the
minor itself, to be zero in `Q(zeta_32)`.

The generic Parseval/AM--GM resultant engine is already axiom-clean as

```text
ArkLib.ProximityGap.KKH26.natAbs_resultant_cyclotomic_sq_le_l2SqOn_pow
```

in `Sweep_A34_LacunaryResultantS128.lean`.  Reducing a length-`32`
group-ring coefficient vector modulo `X^16+1` costs the factor `2` above and
puts the minor in exactly that theorem's degree-`<16` surface.

The anchor is structurally nonzero.  If `e_1(A)=e_1(C)` in characteristic
zero, the dyadic subset-sum collision law forces the two disjoint sets to be
unions of antipodal pairs.  Their cardinalities would be even, contradicting
`|A|=|C|=7`.  This input is already axiom-clean in

```text
Round29IteratedLift.antipodal_closure_unconditional
```

(equivalently, use
`KKH26CharZeroCollisionLaw.sum_eq_iff_freePart_eq`).  Its exact
odd-cardinality corollary is packaged in

```text
_HalfPredecessorRateQuarterOddAnchor.lean
```

As an independent finite check, the exact probe

```text
scripts/probes/probe_rate_quarter_mu32_e1_e6_collision.cpp
```

encodes `e_1` and `e_6` in the integral power basis
`1,zeta,...,zeta^15` using `zeta^(e+16)=-zeta^e`, enumerates all seven-subsets,
and returns

```text
sets=3365856 exact_signature_groups=3074048 max_group=29 disjoint_pairs=0
CERTIFIED
```

Reproduction takes about a second:

```bash
clang++ -O3 -std=c++17 -Wall -Wextra -Wpedantic \
  scripts/probes/probe_rate_quarter_mu32_e1_e6_collision.cpp \
  -o /tmp/probe_mu32_e1e6
/tmp/probe_mu32_e1e6
```

This census proves the stronger statement that disjoint `A,C` cannot share
both `e_1` and `e_6`, but it is not load-bearing: antipodal parity already
gives `x_1 != 0`.  All `e_1`-anchored minors lift to zero in characteristic
zero, making the full coefficient-difference vectors proportional.  The
alleged `P1` triangle is therefore a universal triangle, contradicting the
universal census above.

The exact terminal arithmetic is axiom-clean in

```text
_P1RateQuarterMu32MinorNormBudget.lean
```

The remaining formalization gap is the locator-minor-to-integer-polynomial
encoding, its `l2SqOn <= 548800` bound and resultant-divisibility glue, plus a
kernel-checked replacement for the executable universal census.  The generic
norm engine, antipodal anchor, and terminal integer budget are already Lean
theorems—not mathematical residuals silently assumed proved in Lean.

## Non-affine scalar syzygies are included

The affine parameterization loses no general scalar relations.  If three
monic degree-`d` polynomials satisfy

```text
r P_A + s P_B + t P_C = 0,
```

their leading coefficients give `r+s+t=0`.  If `s != 0`, division by `-s`
is exactly the affine form used by the probe.  For pairwise-disjoint split
locators, a nonzero two-term relation is impossible because monicity would
make the two locators equal.  Therefore every nontrivial three-locator
syzygy can be normalized in one of the searched orientations.

This normalization and the `X -> X^2` four-direction rigidity are formalized
in

```text
_HalfPredecessorRateQuarterOneRootExtensionRigidity.lean
```

with standard axioms only.

## The shared-root false lead

An earlier unrestricted `F_193` search appeared to find a degree-`7` identity:

```text
A={0,1,3,19,20,25,27}
B={2,3,6,14,18,24,28}
C={3,5,7,9,11,13,15}.
```

All three sets contain exponent `3`.  Cancelling the common factor leaves the
degree-`6` triple

```text
A'={0,1,19,20,25,27}
B'={2,6,14,18,24,28}
C'={5,7,9,11,13,15}.
```

Moreover this reduced identity is characteristic-specific: it holds over
`F_193` and fails over `F_97`, `F_257`, `F_353`, and `F_449`.  It supplies no
universal or prize-field lift.

Representative genuine disjoint `F_97` degree-`7` hits were also checked as an
independent sanity test in
the actual prize field

```text
P1 = 365375409332725729550921208179070755120141565953.
```

For example, the `F_97` hit

```text
A={0,2,9,11,14,16,23}
B={1,8,10,19,26,28,31}
C={12,15,20,21,22,27,30}
```

fails coefficient collinearity over `P1`.  This sample is only a sanity check;
the exhaustive `P1` obstruction is the anchored-minor lift above.

## Structural obstruction to every nested quotient extension

Let `A,B` be coprime and let `D=uA+vB`.  Consider arbitrary polynomial
coefficients, not merely linear factors:

```text
A*rA + B*rB + D*rC = 0.
```

Expanding the base identity gives

```text
A*(rA+u*rC) + B*(rB+v*rC) = 0.
```

If

```text
deg(rA+u*rC) < deg(B),
deg(rB+v*rC) < deg(A),
```

Euclid's lemma gives `B | (rA+u*rC)` and `A | (rB+v*rC)`.  The strict degree
bounds force

```text
rA = -u*rC,   rB = -v*rC.
```

Thus the entire new syzygy is the old one times the common multiplier `rC`.
When `u,v` are nonzero, `rA,rB,rC` have exactly the same roots.  Any appended
domain root is therefore present in all three pair differences and is dead
for the disjoint-block ledger.

The axiom-clean formalization is

```text
_HalfPredecessorRateQuarterCoprimeQuotientRigidity.lean
```

and proves both the polynomial identity and the common-root equivalences.

## First `mu_64` boundary-lowering route also fails

The most direct `mu_64` escape was checked after the `mu_32` obstruction was
isolated.  All 72 disjoint degree-four boundary locator triangles on `mu_16`
were lifted through `X -> X^4`, producing degree-16 triangles on `mu_64`.
For every triangle, all `16^3` ways of deleting one root independently from
the three lifted blocks were tested.  None of the resulting disjoint
degree-15 locator triples is affinely collinear over any of `F_193`, `F_257`,
or `F_449`:

```text
72 * 16^3 = 294,912 tests per prime,
0 hits on each prime.
```

This rules out the natural "lift a boundary triangle and remove one root"
construction; it is not a census of all `C(64,15)` root blocks.  The exact
probe is
`scripts/probes/probe_rate_quarter_mu64_boundary_one_root_lowering.py`.

## Honest frontier after this obstruction

The following routes remain logically open:

1. a genuinely non-nested higher-degree triangle at `mu_64` or beyond;
2. a larger-cell identity with `d/B > 3/16`;
3. a different incidence geometry that improves the radius without a split
   locator triangle.

The clean recursive plan “compose the cubic identity, then append independent
roots” is closed by theorem; the universal non-nested degree-`7` `mu_32` plan
is closed by the exact orbit census; and the prize-specific `mu_32` loophole is
closed by the anchored-minor norm lift.
