# Delta-star rate quarter: cocircuits and large-core recursion (2026-07-09)

Status: the far-direction, sharp obtuse-vector, determinant-multiplicity,
collapsed-cluster injection, complementary two-core, core-band synthesis, and
cocircuit-rigidity branches are machine-checked.  At saturated quarter rate
`h=2k`, every counterexample now has a canonical anchored petal package: either
a high core with a petal of size at least `floor(k/2)+3`, or an intermediate
core with a petal of size at least `floor(k/3)+2` and the exact all-partner
isolation inequalities.  Both anchors carry uniform determinant-collapse or
new-coordinate rules.  The remaining step is to control the uncovered
high-core population or iterate enough noncollapsed companion petals.

## Exact reformulation

Let `n=2h`, `k<=h/2`, and let `C=RS[n,k]`.  For a received stack
`(u0,u1)`, put

```text
E = C + span{u0,u1}.
```

Choose a full-agreement polynomial `q_gamma` for every nonjoint bad scalar at
the half predecessor, and write

```text
e_gamma = u0 + gamma*u1 - q_gamma.
```

Then `wt(e_gamma)<=h-1`.  More is true: `e_gamma` is support-minimal in `E`.
Indeed, with lifted coordinate rows

```text
r_x = (u0(x),u1(x),1,x,...,x^(k-1)),
```

the zero set of `e_gamma` is cut out by the decoded normal
`(1,gamma,-coeff(q_gamma))`.  The nonjoint clause says that the lifted rows on
this zero set span the whole kernel hyperplane.  Since the full agreement set
is the complete zero set, its complement is a cocircuit support of the lifted
matroid.  Distinct bad scalars have distinct directions in the two-dimensional
quotient `E/C`.

Thus the live rate-quarter statement is equivalently:

> In a two-dimensional extension of an `[2h,k]` RS code, `k<=h/2`, at most
> `2h` quotient directions can contain a cocircuit of weight at most `h-1`.

The MDS subcode also gives the support hierarchy

```text
d_r(E) >= 2h-k+r-2       for r>=3.
```

because every `r`-subspace of `E` meets the codimension-two subcode `C` in
dimension at least `r-2`.  The stronger hierarchy relevant to the selected
points uses their affine differences: these lie in `C+span{u1}`, a
codimension-one extension of `C`, so an `r`-dimensional difference space meets
`C` in dimension at least `r-1` and has support at least
`2h-k+r-1`.  In the rich-hyperplane language, an affine `r`-flat of decoded
points has common agreement at most `k-r+1`.  The ordinary
noncollinear-triple cap is the `r=2` case.

This recasts the target as a support-minimal-codeword problem, not merely a
union-of-secants problem.  The support-minimal clause is exactly what the known
unrestricted MDS counterexamples omit.

## Large-core recursion

Fix a rich decoded line with joint core `D` of size `z`, and subtract its
polynomial intercept and slope.  Every point outside the line has at most
`k-1` agreements in `D`, hence at least

```text
h+1-(k-1) = h-k+2
```

fresh agreements on `U = domain \ D`.  At the boundary `k=h/2` and at the
packing-sized core `z=h`, this becomes a length-`h`, dimension-`h/2` problem
with agreement threshold `h/2+2`: two lattice steps inside the child half
radius.

The sharp packing family appears recursively as two lines: relative to the
first `h`-core line, all `h` outside points are joint on the complementary
`h`-core and form the second line.  Therefore an induction must separate:

1. outside points that remain nonjoint after restriction to `U`;
2. outside points that become joint on `U`, which necessarily cluster on new
   decoded lines.

This is a more precise target than the earlier three-set Bonferroni collapse,
whose large-core threshold becomes vacuous at rate `1/4`.

## Exact finite red teams

### Smallest possible packing deformation

`scripts/probes/probe_half_predecessor_n12_extension.py` performs an exact
`(n,k,q)=(12,3,13)` census.  The standard packing line realizes all twelve
nonzero scalars with five-error supports.  Keeping those twelve witnesses, it
tests every one of the `C(12,5)=792` supports at the unused scalar zero.

The exact kernel histogram is

```text
extension nullity 1:  12
extension nullity 0: 780.
```

In all twelve nonzero cases, two of the thirteen prescribed witnesses are
forced joint; in the zero-kernel cases all thirteen are forced.  Since at most
`q` proper subspaces cannot cover a finite vector space over `F_q`, this proves
that no deformation of this packing support pattern realizes a thirteenth
nonjoint scalar.

This is not a census over all support patterns, so it is evidence and a local
rigidity theorem, not the general rate-quarter bound.

### Two-step child problem

`scripts/probes/probe_r383_n8k4_e2_exhaustive.py` exhausts all 89,030
projective syndrome lines for the dyadic `[8,4]` RS frame over `F_17`, now at
error weight two (agreement six).  The maximum number of proper points is

```text
7 < 8.
```

The histogram is

```text
0:14376, 1:35256, 2:21640, 3:11064,
4:5958, 5:456, 6:256, 7:24.
```

This sharply contrasts with the one-step child problem at error weight three,
where most projective lines have all eighteen points proper.  It supports the
large-core recursion: the extra one-coordinate slack is structurally real.

## Current proof target

The strongest surviving route is a stability theorem for small cocircuits in a
two-dimensional RS extension:

* either a large decoded-line core exists and the family recursively splits
  into at most two line clusters;
* or the maximum pair core is below the exact Johnson denominator and the
  second-moment inequality closes;
* intermediate cores require an energy increment showing that a new line
  cluster consumes a quantitatively new portion of the coordinate domain.

Any proposed proof must reproduce the two-line packing equality case and must
survive the exact affine-plane witness trade from the Grassmann/Chow audit.

## New exceptional-core hierarchy

The exact Johnson branch can be sharpened geometrically.  Truncate every full
agreement set to exactly `t=h+1` coordinates.  If every pair meets in at most
`k+1` coordinates and `2k<=h`, define the real vector

```text
v_S(x) = n*1_S(x) - (t-1),       n=2h.
```

Its coordinate sum is `n>0`, while for distinct `S,T`

```text
<v_S,v_T> = n * (n*|S intersect T| - (t^2-1)) <= 0,
```

because

```text
n*(k+1) <= 2h*(h/2+1) = (h+1)^2-1.
```

Mathlib contains precisely the needed Rankin/obtuse lemma:
`LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero`.  Vectors with
pairwise nonpositive inner product lying in one open half-space are linearly
independent.  Hence there are at most `dim R^n=n` sets.  This is axiom-clean in
`Frontier/_HalfPredecessorRateQuarterObtuse.lean`, including the literal
bad-event wrapper.  It improves the already checked ordinary-Johnson branch
(`DirectionAgreementCap <= k`) by one full coordinate.

The exact endpoint budget is stronger and independent of `k`.  A uniform pair
cap `s` closes whenever

```text
2s <= h+2.
```

This is `card_le_two_mul_of_pair_inter_le_of_two_mul_cap_le`.  Consequently a
counterexample must contain a pair intersection of size at least
`floor(h/2)+2`, as recorded by
`card_le_two_mul_or_exists_pair_core_ge_half_add_two`.  Under two units of rate
slack (`2k+2<=h`), even the `k+2` band closes and the residual begins at
`k+3`.  Only the saturated or near-saturated rate retains the first band.  At
the prize boundary `h=2k`, the line packing law explains why `k+2` is the first
genuinely new value:

```text
core <= k+1  => every decoded line has at most 2 points;
core =  k+2  => 3-point decoded lines first become possible.
```

The four-witness affine-plane trade from the Grassmann audit has pair cores of
sizes `k+1` and `k+2`, so it lives exactly on this first surviving face.

## Determinant multiplicity for three large decoded lines

Let decoded polynomial lines have core codeword pairs

```text
c_i=(a_i,r_i),       D_i={x : (u0(x),u1(x))=c_i(x)}.
```

For three lines form

```text
Delta_123 = det(c_2-c_1, c_3-c_1).
```

Both entries of every `c_i` have degree `<k`, so

```text
deg Delta_123 <= 2k-2.
```

At a coordinate in exactly two of the cores, one polynomial difference has a
common linear factor, so `Delta_123` vanishes once.  At a coordinate in all
three cores, both columns vanish and the determinant has a double zero.  The
total certified root multiplicity is therefore

```text
sum_x max(coreMultiplicity(x)-1,0)
  = |D_1|+|D_2|+|D_3|-|D_1 union D_2 union D_3|
  >= |D_1|+|D_2|+|D_3|-n.
```

Consequently

```text
|D_1|+|D_2|+|D_3|-n > 2k-2  =>  Delta_123=0.       (DC)
```

This criterion is now axiom-clean in
`Frontier/_HalfPredecessorRateQuarterDeterminantMultiplicity.lean` as
`threeLineDeterminant_eq_zero_of_core_card_sum_sub_domain_gt`.  Its local
`coreCount_sub_one_le_rootMultiplicity` theorem proves the simple- and
double-root contributions directly, and
`sum_coreCount_sub_one_le_natDegree` performs the injective-domain root count.
The equivalent decoded-line API in
`Frontier/_HalfPredecessorRateQuarterDeterminantCollapse.lean` exposes the
weighted overlap budget and determinant-zero conclusion for direct composition
with the cluster argument below.

The conclusion says that the three polynomial pairs lie on one rational
affine line over `F(X)`.  Write, after removing a primitive common vector,

```text
c_i = c_0 + f_i*(A,R).
```

If a coordinate carries core `c_j` and supplies a fresh petal for decoded line
`i`, the scalar equation cancels `f_j-f_i` and reads

```text
gamma = -A(x)/R(x),
```

independent of both `i` and `j` (denominator-zero coordinates supply no
transverse petal).  Thus every cross-line scalar in a rationally collinear
cluster is read from one common coordinate function.  Distinct scalars choose
distinct coordinates, giving the desired `<=n` injection for that cluster.

This consequence is now formal in
`Frontier/_HalfPredecessorRateQuarterCollapsedClusterInjection.lean`.
`card_le_domain_of_collapsed_fresh_petals` proves the exact conditional
statement: determinant collapse against a fixed reference pair, a nonzero
reference slope difference, and one agreement coordinate in another line's
core but outside the source core give an injection into the coordinate
domain.  The remaining global task is to construct such a fresh transverse
petal for every scalar, or to charge all scalars for which none exists.
The literal local bridge
`Frontier/_HalfPredecessorRateQuarterCrossCoreScalar.lean` removes a separate
transversality assumption: cross-core agreement outside the source core forces
the slope difference to be nonzero and proves the exact scalar-ratio identity
at that coordinate.

`Frontier/_HalfPredecessorRateQuarterFreshPetalAssembly.lean` removes the
explicit target and coordinate choices under a core-union coverage budget.
If every source core plus the coordinates missed by the collapsed cluster's
core union has size at most `h`, richness forces a fresh cross-core petal; the
module chooses the target and coordinate internally and concludes `|G|<=n`.

### Counterconstruction that collapses to the invariant

An explicit attempted three-line construction confirms the mechanism.  Let
`n=4k`, choose scalar degree-`k/2` polynomials `f_1,f_2,f_3` whose three
pairwise differences split on three disjoint `k/2`-cosets of the dyadic
domain, and choose a common factor `G` of degree `k/2-2`.  The codeword pairs

```text
c_i = f_i*G*(1,X)
```

have degree `<k`; their pair equality cores have size `k-2`, and three
`2k`-element received-word cores fit combinatorially in the `4k` coordinates.
Nevertheless every petal scalar is

```text
gamma=-1/x,
```

for all three decoded lines.  Their apparent `3h` line capacity collapses to
at most the `n` coordinate values.  This red team supports `(DC)` as the right
large-core stability invariant rather than a bare set-system moment bound.

The remaining task is to combine the obtuse `k+1` branch, determinant-collapse
clusters, and a weighted pruning bound for the intermediate cores not large
enough to trigger `(DC)`.

The exact localization is itself now a Lean theorem:

```text
card_le_two_mul_or_exists_large_pair
```

It states that every selected rich-point family either has cardinality at most
`2h=n`, or contains distinct selected scalars whose full-agreement intersection
has cardinality at least `k+2`.  The stronger rate-independent theorem above
raises this to `floor(h/2)+2`.  Thus no global direction-cap predicate is part
of the remaining conjectural branch.

## Complementary two-core branch

`Frontier/_HalfPredecessorRateQuarterComplementaryCores.lean` closes the exact
packing/extremizer geometry.  If two relevant decoded-line joint cores cover
the coordinate universe, then every selected point lies on one of those two
lines: a point off both lines meets each core in at most `k-1` coordinates, so
it has at most `2(k-1)<h+1` agreements.  The theorem
`card_le_two_mul_of_core_union_eq_univ` then applies line-core packing to both
lines and proves `|G|<=2h`.

The quantitative theorem `card_le_two_mul_of_small_core_complement` allows an
uncovered set `R` whenever `|R|+2(k-1)<h+1`.  In particular, at the saturated
boundary `h=2k`, two relevant cores may miss two coordinates and still force
the sharp bound.  If both cores have size `h`, any surviving pair therefore
has overlap at least three (while distinct decoded cores meet in at most
`k-1`).

Thus a counterexample cannot be a deformation that preserves two
complementary cores.  Exact small-case probes agree: all `11,440` one-point
extensions of the `F17`, `[16,4]` packing force jointness; an exhaustive
one-witness trade census over `246,016` positive-dimension candidates and all
`5,184` best two-trade neighbors finds no nonjoint extension.  These are local
stability checks, not a full `F17` infeasibility certificate.  In particular,
the current full-line Z3 runs return `unknown` and the MILP reaches a time
limit without an incumbent; their exit status must not be reported as a proof.

The first surviving saturated boundary, where two half cores overlap in
exactly three coordinates, is now rigid in
`Frontier/_HalfPredecessorRateQuarterOverlapThreeRigidity.lean`.  Every point
off both lines has exactly `h+1` agreements, saturates both `k-1` root caps,
avoids the common three-coordinate core, and contains all three coordinates
outside the two-core union.  The companion
`Frontier/_HalfPredecessorRateQuarterOverlapThreeFactorization.lean` proves
that the two off-line residual polynomials are nonzero scalar multiples of
their monic degree-`k-1` root locators and reconciles the two blocks with the
exact affine difference of the decoded lines.  The companion
`Frontier/_HalfPredecessorRateQuarterOverlapThreeCommonFactor.lean` factors
both decoded-line differences through the cubic locator of the common core,
leaving quotient degrees below `k-3`.  Its reconciliation identity is an
exact cubic recursive form, but it does not yet construct a smaller bad
family.  Finally,
`Frontier/_HalfPredecessorRateQuarterOverlapThreeAnchorRigidity.lean` proves
that the two saturated locator quotients agree on the three distinct
common-core anchors.  Three quotient collisions do not by themselves force
degree-`k-1` locators to coincide, so this is a boundary constraint rather
than a closure theorem.

The cocircuit reformulation cannot close the count without this polynomial
structure.  `Frontier/_HalfPredecessorRateQuarterAbstractCocircuitRefuted.lean`
checks a `K8` cut-family core with 36 distinct affine short-support coordinates
on 28 edges, all below half weight and in the quarter-rate rank regime.  The
cut-support facts and affine chart are kernel-checked; the separate probe
checks that the displayed supports are cocircuits.  This refutes the bare
abstract cocircuit-count strategy, not the Reed--Solomon theorem.

## Exact remaining dichotomy

`Frontier/_HalfPredecessorRateQuarterCoreBandSynthesis.lean` now composes the
obtuse, complementary-core, and large-core-collapse arguments.  Its theorem
`card_le_two_mul_or_high_core_or_intermediate_core_without_complement` says
that a family larger than `2h` must enter at least one of two residual regimes:

```text
high core:          some relevant core has size at least h;
intermediate core:  some relevant core has size in [floor(h/2)+2,h-1],
                    and its union with every relevant core misses >=3 points.
```

`Frontier/_HalfPredecessorRateQuarterGlobalPetalSynthesis.lean` packages the
next handoff unconditionally.  Either `|G|<=2h`, a high core has a petal of
size at least `floor(k/2)+3`, or an intermediate core has a petal of size at
least `floor(k/3)+2` together with the failed-cover data.  This is canonical
plumbing between the band theorem and the pruning theorems; neither surviving
petal alternative is contradictory on its own.

In the high-core regime, any three relevant cores of size at least `h` satisfy
the determinant-collapse relation, by
`lineDeterminant_eq_zero_of_three_relevant_half_core_lines`.  What remains is
the global supply step: choose a fresh cross-core agreement coordinate for
each selected scalar, or charge the scalars with no such coordinate.

`Frontier/_HalfPredecessorRateQuarterFreshPetalAssembly.lean` closes the
existential part under an exact coverage inequality.  If the source-core size
plus the number of coordinates missed by the union of a collapsed target
cluster is at most `h`, every `h+1` agreement set has a fresh coordinate in a
different target core.  If the fixed reference slope difference is transverse
there, the resulting coordinate assignment is injective.

The stronger family-level reduction in
`Frontier/_HalfPredecessorRateQuarterHighCoreFreshPetalDichotomy.lean` uses a
degree root count: `k` fresh cross-core coordinates are enough to find one
outside the zero set of a nonzero reference slope difference.  Given two
relevant cores of size at least `h`, the high-core branch therefore reduces to
four explicit outcomes:

```text
equal reference slopes;
|G| <= 2h;
a scalar on no relevant >=h-core line;
a scalar with <=k-1 fresh coordinates in every relevant >=h target core.
```

At this stage of the reduction, the unresolved high-core work is no longer
determinant algebra or choice construction.  It is the equal-slope case and
the global cover/starvation alternatives; the modules below sharpen both.

`Frontier/_HalfPredecessorRateQuarterHighCorePetalGrowth.lean` also attacks
the branch before a second half core is available.  At `h=2k`, one relevant
core of size at least `h` in a counterexample forces a secant petal of size at
least `floor(k/2)+3` outside that core.  More generally, the reduced-universe
Rankin budget with cap `h-1` produces a distinct second half core.  The theorem
`second_high_core_or_reduced_budget_failure` retains the exact arithmetic
failure when that budget does not hold, so the one-high-core residual is now
an explicit reduced-universe capacity obstruction rather than a missing
selection step.

`Frontier/_HalfPredecessorRateQuarterHighCoreReducedBudgetBarrier.lean`
shows that this obstruction is automatic throughout the globally surviving
high-core band.  For `0<k` and `2k<=z<=3k-4`, it proves the strict reverse

```text
(k+2)^2 - 1 < (4k-z)(2k-1)
```

of the cap-`h-1` Rankin premise.  Thus the complete-residual theorem is
diagnostic on this branch: its reduced-budget alternative cannot be reused
to manufacture a second half core without a sharper cap or a different
argument.

For the non-equal-slope branch,
`Frontier/_HalfPredecessorRateQuarterHighCoreUnionSupply.lean` replaces local
target starvation by an aggregate condition.  It is enough to have `k` fresh
agreements across the union of all half cores; the degree root bound selects a
transverse coordinate in some target.  The exact failure set for a source is

```text
source core union reference-slope roots union coordinates missed by all half cores.
```

If this set is smaller than the source agreement set, coordinate injection
closes the family.  The remaining non-equal-slope obstruction is therefore one
explicit set-capacity inequality, plus the possibility that a scalar lies on
no half-core line.

`Frontier/_HalfPredecessorRateQuarterEqualSlopeHighCores.lean` further reduces
the equal-slope case.  Two distinct equal-slope half cores force the received
direction row to disagree with their common degree-`<k` slope polynomial on at
most `k-1` coordinates.  Determinant collapse propagates that slope to every
other relevant half-core line, and disjoint fresh fibres then give

```text
pointsOn(line) <= k-1,
halfCoreCoveredScalars <= (# half-core lines)(k-1).
```

`Frontier/_HalfPredecessorRateQuarterEqualSlopeJohnsonClosure.lean` closes the
covered population sharply.  If `e` is the common direction-disagreement
count and `L` is the number of half-core lines, truncating every core to size
`2k` in the common `4k-e` coordinate universe and applying sharp Johnson gives

```text
L * (4k + e(k-1)) <= (4k-e)(k+1),
L * e <= 4k.
```

Hence at most `4k=2h` selected scalars lie on half-core lines.  The branch with
two distinct equal-slope half cores and a half-core cover of `G` is therefore
closed.  Its exact residual is now scalars outside every half-core line,
together with the separate one-half-core/no-distinct-reference case.

`Frontier/_HalfPredecessorRateQuarterHighCoreUnifiedClosure.lean` combines
this Johnson closure with the aggregate-union theorem.  Given two distinct
half-core references, it exports one trichotomy:

```text
|G| <= 2h;
some selected scalar lies on no half-core line;
the reference slopes differ and a covered scalar satisfies the explicit
forbidden-capacity inequality.
```

Thus equal reference slopes are no longer a live covered branch.  The
one-reference case, uncovered scalars, and the displayed non-equal-slope
capacity witness are the exact high-core residuals.

`Frontier/_HalfPredecessorRateQuarterHighCoreCompleteResidual.lean` also
eliminates the vague one-reference handoff.  Starting from one half core in a
counterexample, it composes the reduced-budget dichotomy with the unified
two-reference theorem.  At least one of three explicit obstructions survives:
the reduced-universe budget for a second half core fails; a selected scalar
is uncovered by every half-core line; or two unequal-slope references exist
and a covered scalar satisfies the forbidden-capacity inequality.  This is a
complete residual classification, not a proof that the three obstructions
are impossible.

The first obstruction is in fact automatic throughout the surviving global
high-core band.  The exact arithmetic in
`Frontier/_HalfPredecessorRateQuarterHighCoreReducedBudgetBarrier.lean` proves
that `h=2k` and `h<=|D|<=3k-4` force the strict reverse of the cap-`h-1`
budget used to obtain a second half core.  Thus that particular conditional
bridge is unavailable everywhere it would be needed.  A second-core argument
must use a sharper cap or different geometry; the barrier does not say that a
second half core cannot exist.

`Frontier/_HalfPredecessorRateQuarterHighCoreSharpSecantExtraction.lean`
supplies that different geometry without reusing the failed cap.  For a source
core of size `z`, it takes the largest admissible reduced Rankin cap

```text
s = floor(((k+2)^2-1)/(4k-z))
```

and forces an outsider secant petal of size at least `s+1`.  This sharp
threshold dominates the previous `floor(k/2)+3` bound throughout the surviving
high-core band.  At the maximal stratum `z=3k-4`, the petal and complement are
forced exactly:

```text
|D2 \ D| = k+1,    |univ \ (D union D2)| = 3.
```

Thus the top high-core branch either produces a second half core or reduces to
an exact three-hole secant with `|D inter D2|<=k-2`.  This is a sharper residual,
not a global rate-quarter closure.

At the base case `n=16,k=4`,
`Frontier/_HalfPredecessorRateQuarterKFourLongOutsiderCollapse.lean` sharpens
the one-high-core population directly.  Two outsiders with at least seven
fresh agreements beyond a size-eight source core have fresh intersection at
least six inside the eight-point complement.  Their secant and the source core
therefore miss at most two coordinates, so the complementary-core theorem
forces `|G|<=16`.  Consequently, in any counterexample:

```text
# {outsiders with fresh >= 7} <= 1;
# {outsiders with full agreement >= 10} <= 1;
# regular outsiders >= 8.
```

Every regular outsider saturates the split exactly as `9=6+3`: six fresh
agreements and three agreements in the source core.  This turns the remaining
one-high-core base case into a concrete paired signature problem rather than
an unrestricted population question.

The first surviving two-half-core overlap cell is also exact.
`Frontier/_HalfPredecessorRateQuarterOverlapThreeRigidity.lean` proves that
when two size-`h` cores intersect in exactly three coordinates at `h=2k`, any
rich point off both decoded lines must attain equality everywhere: it uses all
three coordinates outside the core union, avoids the three-point core
intersection, and meets each core in exactly `k-1` coordinates.  Thus both
off-line polynomial root caps saturate.
`Frontier/_HalfPredecessorRateQuarterOverlapThreeFactorization.lean` turns
each saturated residual into its nonzero leading coefficient times the monic
degree-`k-1` locator of its root block and proves the two-block reconciliation
identity.  The common three coordinates then give two further exact forms:

* `_HalfPredecessorRateQuarterOverlapThreeCommonFactor.lean` factors both
  decoded-line differences through the common cubic locator and lowers the
  quotient pencil degree to `<k-3`;
* `_HalfPredecessorRateQuarterOverlapThreeAnchorRigidity.lean` proves the two
  locator values are nonzero and have one constant quotient at all three
  distinct common-core anchors.

For the base case `k=4`, length `16`,
`Frontier/_HalfPredecessorRateQuarterOverlapThreeKFour.lean` goes further:
the quotient degree bound is `<1`, so both decoded-line differences are
constant multiples of the common cubic locator.  Distinct decoded lines then
have at most one common scalar parameter.

`Frontier/_HalfPredecessorRateQuarterOverlapThreeKFourPopulation.lean` turns
that shape into a population theorem.  Compatible three-root blocks across a
five-coordinate petal form a matching.  Consequently, for two size-eight
cores meeting in three coordinates, threshold at least nine, and the explicit
global cap that every relevant core has size at most eight, there are at most
ten selected points off both decoded lines.  If the two reference slopes are
equal, the existing half-core estimate leaves at most three points on each
line, so

```text
|G| <= 10 + 3 + 3 = 16.
```

`Frontier/_HalfPredecessorRateQuarterOverlapThreeKFourUnequalResidual.lean`
first bounds the entire reference-line union by seven.  Its exact saturation
theorem shows that any remaining `|G|>16` case would have population
`17=3+3+1+10` and unequal reference slopes.

`Frontier/_HalfPredecessorRateQuarterOverlapThreeKFourUnequalClosure.lean`
eliminates that last point.  For unequal slopes, the secant through two
off-both points has nonzero determinant with the two references.  If their
three-root blocks overlapped in two coordinates in both five-point petals,
the weighted overlap `3+2+2=7` would force the same determinant to vanish.
If all ten off-both signatures existed, both root-block maps would be
bijections onto the ten three-subsets of a five-set.  Every triple has six
overlap-two neighbours; two such six-element neighbourhoods inside the nine
remaining indices must meet, producing the forbidden double overlap.  Hence

```text
offBoth <= 9,    referenceUnion <= 7,    |G| <= 16.
```

This closes both slope branches of the `n=16`, `k=4`, overlap-three/cap-eight
cell.  It does not by itself close the one-high-core, intermediate-core, or
higher-length rate-quarter branches.

`Frontier/_HalfPredecessorRateQuarterKFourGlobalCoreSynthesis.lean` composes
that cell with the full base-case core band.  Distinct relevant eight-cores
always close: overlap at most two uses the complementary-core theorem, overlap
three uses the locator closure above, and overlap greater than three violates
the degree-three root cap.  The exact global `n=16,k=4` residual is therefore:

```text
|G| <= 16;
or one unique eight-core plus a distinct exact three-hole core of size 5/6/7
   and at least eight regular outsiders;
or no eight-core, a source core of size 6/7, global core cap 7,
   every partner leaving at least three coordinates uncovered,
   and an outsider secant petal of size at least three.
```

All multi-high-core cases are now closed.  The remaining base-case work is
precisely the unique-high/sub-high signature configuration and the globally
no-high intermediate configuration.

`Frontier/_HalfPredecessorRateQuarterKFourLongOutsiderCollapse.lean` gives an
independent structural funnel around any size-eight source core.  In a
counterexample at threshold at least nine, at most one outsider has seven
fresh agreements, hence at most one has ten full agreements; at least eight
outsiders are therefore regular and attain the exact split `9=6+3` between
fresh agreements and the source core.  This sharpens the remaining `k=4`
one-high-core population but is not itself a contradiction.

`Frontier/_HalfPredecessorRateQuarterKFourRegularSignatureRigidity.lean`
adds a genuinely polynomial constraint to that population.  A regular outsider
has a three-coordinate root block in the source core and misses a two-edge in
the eight-coordinate complement.  Three distinct outsiders with the same root
block cannot have pairwise-disjoint missed edges: their cubic residuals are
scalar multiples of one locator, and an affine-row filling argument would
otherwise turn every miss into an agreement.  Two intersecting missed edges
leave at least five common fresh agreements, so their secant produces another
core of size at least eight, meeting the source core in exactly three
coordinates.  Under the global cap this core has size exactly eight; combined
with the global two-eight-core closure, every root block therefore has
multiplicity at most two in a surviving unique-eight-core counterexample.
This still does not close the branch: eight regular outsiders may occupy eight
of the 56 possible root triples.

The separate line-list attack in
`Frontier/_HalfPredecessorRateQuarterSparseSafeLine.lean` uses the generic
exact-diagonal bound from `_ConstantWeightPlotkinBound.lean`.  At
`n=16,k=4,a=9`, every zero-safe direction of support at most two has at most
fourteen bad scalars, with exact endpoints `0`, `3`, and `14` for support
`0`, `1`, and `2`.  The positive Plotkin denominator fails at the first
support-three stratum `(z,t,lambda)=(13,6,3)`, so this is an honest sparse
slice rather than a uniform line-list closure.  The full derivation is in
`docs/kb/deltastar-466-rate-quarter-sparse-safe-plotkin-2026-07-09.md`.

In the intermediate regime, a bare two-core cover cannot close the argument.
The remaining target is a weighted pruning inequality that charges the
uncovered coordinates and the points lying on lines with cores below `h`.
The strengthened synthesis theorem also proves, for every relevant residual
core `D`,

```text
2|D|+3 <= h+4(k-1).
```

At the saturated boundary `h=2k`, this is the integral ceiling
`|D|<=3k-4`.  Hence the two live bands are exactly
`[2k,3k-4]` and `[k+2,2k-1]`; larger cores already contradict the sharp
large-core inequality.

`Frontier/_HalfPredecessorRateQuarterFreshPetalPruning.lean` adds a genuine
increment in the intermediate band.  For a proper core `D`, every integer `s`
satisfying

```text
(2h-|D|)s <= (h+1-(k-1))^2-1
```

must be exceeded by the fresh petal of some secant through two points outside
the line, unless `|G|<=2h`.  At `h=2k` and `|D|>=k+2`, this forces a new petal
of size at least `floor(k/3)+2`.  Conversely, the uniform cap
`petal<=floor(k/3)+1` closes the whole intermediate branch.  This pruning
theorem alone leaves the overlap issue: it forces a large new petal, but does
not show that successive petals grow their union or trigger determinant
collapse.

`Frontier/_HalfPredecessorRateQuarterPetalOverlapGrowth.lean` now supplies the
exact missing recurrence.  For reference core `D0` and target petals
`Pi=Di\D0`, the determinant weighted overlap is

```text
|D0 inter D1| + |D0 inter D2| + |P1 inter P2|.
```

Consequently a noncollapsed triple has the sharp corresponding petal-overlap
cap; exceeding it forces determinant collapse.  For three petals, unless one
reference-pair determinant collapses,

```text
sum |Pi| + 2 sum |D0 inter Di|
  <= |P1 union P2 union P3| + 6(k-1).
```

The overlap recurrence alone therefore leaves a selection problem: produce
several forced petals with controlled determinant status or sufficiently
large base intersections so the recurrence outgrows the coordinate
complement.  The next module removes the anchor-compatibility part of that
problem.

`Frontier/_HalfPredecessorRateQuarterPetalIteration.lean` rewrites the union
bounds as genuine new-coordinate increments outside a selected anchor.  Its
one- and two-companion rules hold uniformly for every later canonical secant,
modulo the explicit determinant-collapse alternatives.
`Frontier/_HalfPredecessorRateQuarterGlobalPetalSynthesis.lean` first combines
the core-band split with the high- and intermediate-core pruning estimates;
`Frontier/_HalfPredecessorRateQuarterGlobalAnchoredPetalSynthesis.lean` then
attaches both uniform companion rules to the same forced petal.  Consequently
every counterexample has one of the following complete packages:

```text
high:          2k <= |D| <= 3k-4,  |P| >= floor(k/2)+3;
intermediate:  k+2 <= |D| <= 2k-1, |P| >= floor(k/3)+2,
               every partner misses at least three coordinates;
both:          uniform one- and two-companion collapse-or-increment rules.
```

No further anchor-compatibility hypothesis remains.  What is still open is
a global construction of enough companions whose noncollapse charges force
their new-coordinate union beyond the source-core complement.

That construction cannot follow from the current cardinal inequalities
alone.  `Frontier/_HalfPredecessorRateQuarterPetalSelectionRefuted.lean`
checks an abstract `k=7`, `n=28` sunflower with a common kernel of size
`k-1=6` and four disjoint petals of size `floor(k/3)+2=4`.  Every core lies in
the saturated intermediate band; each displayed overlap, petal-growth, and
anchored companion bound holds at equality.  Nevertheless the three
companion petals cover only `12` of the `18` coordinates outside the anchor
core, and every two cores still miss at least three coordinates.  Its
independent `4k+1` labels are not attached to secants, so it refutes only a
cardinal-only selection deduction.

The core geometry itself is Reed--Solomon-realizable.  The exact executable
certificate `scripts/probes/probe_rate_quarter_sunflower_rs_realization.cpp`
constructs an `F29`, `n=28`, `k=7` instance with four degree-six decoded
lines having precisely the `6+4` sunflower cores; all four triple determinants
are nonzero.  Six pair-crossing scalars are nonjoint with exactly 15
agreements, so every displayed line is a genuine three-point secant.
Exhaustive interpolation over all `C(28,7)=1,184,040` information sets and all
29 scalars finds exactly those six candidates and no off-line extras.  Hence
this realization is far below `|G|>28`: line packing permits at most 12 points
on the four lines, and a threatening realization would need at least 17
selected points off all four.  A successful endgame must therefore control
that off-line population, not merely exclude the sunflower cores.  This is a
native exhaustive certificate, checked with warning-clean and sanitizer
builds, not a Lean-kernel theorem.

`Frontier/_R396PolynomialLinePluckerSyzygy.lean` formalizes the exact
determinant cocycle, two componentwise Plucker syzygies, and pointwise
zero-propagation away from a vanishing reference component.  These identities
do not exclude the realized sunflower: its lines have the form
`L_i=(a_i H,r_i H)`, so every nonzero triple determinant is `c_ijk H^2` and
exactly saturates the `2(k-1)` root budget.  At the six roots of `H` the
nonzero-component premise fails; away from them the determinant-zero premises
fail.  The next algebraic input therefore needs off-line population or strict
root surplus, not Plucker compatibility alone.

## Cocircuit reformulation

`Frontier/_HalfPredecessorRateQuarterCocircuitRigidity.lean` proves that each
selected error support is support-minimal in the two-row extension of the
Reed--Solomon code: every extension-code word supported inside it is a scalar
multiple of it.  Thus every selected witness is a genuine cocircuit.  Two
cocircuit elimination alone only regenerates the decoded secant line and its
petal partition.  Moreover, the abstract majority-cocircuit bound is false
even for simple representable matroids at the same rank ratio, so any viable
count must retain the Reed--Solomon/Vandermonde subcode structure.  The exact
certificate is in
`Frontier/_HalfPredecessorRateQuarterAbstractCocircuitRefuted.lean`: the
simple graphic `K8` representation over `F59` has ground size `28`, rank `7`,
and `36` distinct affine-gamma cocircuits of weights `7` or `12`, all strictly
below half.  `scripts/probes/probe_rate_quarter_k8_cocircuit_counterexample.py`
independently verifies rank, support minimality, weights, and affine-chart
injectivity.

## Direction puncture and cross-triple refinement (2026-07-10)

The base-case residual now carries an independent exceptional-direction
certificate.  In
`Frontier/_HalfPredecessorRateQuarterExceptionalDirectionPuncture.lean`, every
`n=16`, `k=4`, threshold-nine counterexample has a degree-below-four
polynomial `r` whose direction-agreement core `Z` satisfies

```text
6 <= |Z| <= 13,
```

and every selected scalar has a full-agreement coordinate outside `Z`.
Direction cores of size at least fourteen are already excluded by the exact
fiber/Plotkin count.  The global composition in
`_HalfPredecessorRateQuarterDirectionCapGlobalConsumer.lean` attaches this
same certificate to both surviving core residuals.  The remaining band is
honest: its direct trace weight is `|Z|-7`, and throughout `6<=|Z|<=13` the
Plotkin gap has the wrong sign,

```text
(|Z|-7)^2 <= 3|Z|.
```

The direction is nevertheless forced to align near the top of the band.
`_HalfPredecessorRateQuarterDirectionSourceAlignment.lean` proves that a
source core of size `c` and direction core of size `z` have the same slope
whenever `c+z>=20`.  Thus a unique eight-core aligns for `z>=12`, and a
size-seven no-eight source aligns at `z=13`.  These are structural
reductions, not population bounds for the aligned cases.

The eight regular outsiders in the unique-eight residual also force a new
secant.  `_HalfPredecessorRateQuarterKFourCrossTripleCollinearity.lean` proves
that among their eight missed two-edges there are three with union of size at
most four.  The corresponding three lifted points are collinear, and their
secant core has size at least six.  Under the core-eight ceiling this gives
either a second eight-core or a core of size six or seven.

`_HalfPredecessorRateQuarterKFourCrossTripleUniqueCoreConsumer.lean` removes
the second-eight branch and makes the surviving arithmetic exact.  In a
counterexample with a unique source eight-core, the forced secant is one of

```text
core 6, source overlap 1, uncovered coordinates 3;
core 6, source overlap 2, uncovered coordinates 4;
core 7, source overlap 2, uncovered coordinates 3.
```

Overlap three would put the three regular outsiders on one source-root
triple; regular-signature rigidity would then create a second eight-core.

`_HalfPredecessorRateQuarterKFourSevenCoreOverlapTwo.lean` now controls both
three-hole alternatives.  After interpolating the three common holes, every
off-secant polynomial lies in one affine two-plane modulo the monic cubic
hole locator.  Four such survivors cannot be collinear: their source-petal
and secant-petal triples would have fixed pairwise intersections, and deleting
those fixed parts gives incompatible disjoint-packing inequalities on grounds
of sizes at most seven and five.  Therefore each of the five secant-petal
coordinates is used by at most three survivors.  Every survivor uses exactly
three, so double counting gives

```text
4 <= # regular outsiders off both lines <= 5.
```

`_HalfPredecessorRateQuarterKFourCrossTripleThreeHoleConsumer.lean` rebases
the forced cross secant as the distinguished residual line and composes that
population theorem.  The unique-eight branch is now reduced to either the
displayed four-or-five population in the `core 6 / overlap 1 / holes 3` and
`core 7 / overlap 2 / holes 3` cells, or exactly

```text
core 6, source overlap 2, uncovered coordinates 4,
every selected point off both lines uses at least 3 of the 4 holes.
```

The last cell is the same four cubic-locator-class interaction that appears
in the support-four size-six line stratum below.  Neither the four-or-five
population alternative nor the four-hole alternative currently closes the
global unique-core branch.

`_HalfPredecessorRateQuarterKFourFourHoleClasses.lean` makes that last wall
literal.  Off-both points using all four holes lie on the polynomial line
obtained by four-point interpolation of the received rows, and there are at
most four of them.  Every other off-both point omits a unique hole.  The
remaining population is the disjoint union of four omitted-hole classes, and
each class has a canonical affine-line-plus-cubic-locator normal form on the
other three holes.  The global consumer now returns either the three-hole
four-or-five population alternative or this exact `FourHoleFourClassWall`.
No aggregate bound across the four omitted-hole classes is currently known.

`_HalfPredecessorRateQuarterKFourSharedHolePrimitive.lean` gives a separate
handoff from the same shared-hole geometry to primitive injection.  The three
holes lie inside every pair-secant core formed by two off-distinguished-secant
regular outsiders, so they cannot serve as fresh coordinates for that pair
source.  On the other hand, each such outsider has at least two agreements
outside the pair core, and those agreements are disjoint from the holes.
The residual therefore supplies four outsiders, each with a partner that
escapes the hole trap.  This removes one primitive-assignment alternative but
does not put the escaping coordinates into target cores from one common
determinant-collapsed cluster, so it is not a closure.

The punctured-syndrome view supplies an independent reduction of the same
unique-eight residual.  In
`_HalfPredecessorRateQuarterKFourUniqueCoreSyndrome.lean`, every regular
outsider becomes a weight-two representation in the quotient of the
complementary `RS[8,4]` code.  If the two quotient received rows are
independent and their plane contains no coordinate column, the strict chord
count gives at most seven regular outsiders, contradicting the residual's
eight.  Hence the quotient rows are dependent or their plane contains a
coordinate column.

`_HalfPredecessorRateQuarterKFourSyndromeDegeneracy.lean` makes both
exceptions concrete.  Dependent rows lift a degree-below-four direction core
of size at least six and route directly into the exceptional direction band.
For independent rows, a column at infinity gives a direction core of size at
least seven; a finite column is an affine weight-one quotient point.  Exactly
one contained column is impossible in the unique-core residual, so the
remaining column branch requires at least two contained columns, equivalently
a common-edge configuration.  This is a sharp residual classification, not a
population closure.

The sparse-line lane now reaches one stratum farther than the earlier
support-at-most-two theorem.
`_HalfPredecessorRateQuarterSupportThreeSafeLine.lean` proves that every
zero-safe `RS[16,4]` line with direction support exactly three has at most
sixteen bad scalars.  On the thirteen zero coordinates, strata of trace sizes
six, seven, and eight carry scalar weights one, one, and three.  Plotkin gives
caps five and two for the upper strata.  The size-six stratum is represented
by six-rich points in an affine-function arrangement; equality classes have
size at most three, so ordered-pair packing gives a cap of eight.  If the
size-eight stratum has two members, their traces cover all thirteen
coordinates with a common triple, every size-six trace avoids that triple,
and a ten-coordinate Plotkin count improves the cap to five.  The two cases
are therefore

```text
8 + 5 + 3 <= 16;
5 + 5 + 6 <= 16.
```

This closes zero-safe supports zero through three.  It does not show that an
arbitrary direction can be reduced to support three, and therefore does not
close the global rate-quarter instance.

The next support is now localized as well.
`_HalfPredecessorRateQuarterSupportFourSafeLine.lean` proves that the
size-five zero-agreement stratum has at most four codewords.  Such a codeword
must use all four moving coordinates at one scalar, so four-point
interpolation puts it on a polynomial line `A+gamma R`.  Distinct traces have
one common kernel, the zero set of a nonzero cubic `R`, of size at most three;
outside that kernel their five-sets are disjoint in the twelve zero
coordinates.  The same module gives a Plotkin cap three at trace size seven;
a direct union count sharpens the trace-size-eight cap to one.  With scalar
weights one, two, and four, the exact current budget is

```text
#bad scalars <= (# size-six stratum) + 14.
```

The size-six Plotkin denominator is exactly zero (`6^2=12*3`).  The subfamily
using all four moving coordinates is again a common-kernel polynomial line
and has size at most three.  Every remaining codeword has an exact
three-of-four support fiber, producing four possible cubic-locator classes.
Controlling that cross-class interaction, together with its coupling to the
upper strata, is the open input inside this support-four module.

A proposed cap of four for the entire size-six stratum is false, even under
zero-direction safety.
`_HalfPredecessorRateQuarterSupportFourSixStratumRefuted.lean` gives an
explicit smooth-domain certificate over `F_17^*`.  On the twelve fixed
coordinates the received offset is the evaluation of

```text
W(X) = X^8 + 7 X^7 + 14 X^6 + 10 X^5 + 3 X^4.
```

For every degree-below-four `p`, the nonzero polynomial `W-p` has degree
eight, so it cannot agree with the fixed offset on nine coordinates.  The
line is therefore zero-safe.  Nevertheless five distinct codewords lie in
the size-six stratum, using heavy scalars `{2,5,10,12,15}` and exact
three-of-four moving fibers.  The exhaustive companion probe
`scripts/probes/probe_rate_quarter_support4_t6_f17.py` finds no other
appearing stratum and exactly those five bad scalars.  Thus the certificate
refutes the stratum-four lever, not the desired line bound of sixteen.

More importantly, the half-predecessor `n`-scalar law itself is false at the
next dyadic rate-quarter length.
`_HalfPredecessorRateQuarterSmoothCounterexampleF97.lean` is a kernel-checked
certificate on the genuine order-32 subgroup of `F_97`, with `n=32`, `k=8`,
radius `15/32`, and agreement threshold 17.  Three degree-below-eight decoded
lines have sixteen-coordinate cores.  For 36 distinct scalars, one of those
cores plus one explicit fresh coordinate supplies a nonjoint MCA witness.
Consequently

```text
32 < # {gamma : F_97 | mcaEvent RS[32,8] (15/32) u0 u1 gamma}.
```

This formally refutes the proposed universal `#bad<=n` half-predecessor
extension from rates `1/8` and `1/16` to rate `1/4`.  The fibre construction
also has an exact executable lift at the first prize-shaped prime.  It has
`(9/8)n` bad scalars at the half predecessor and, after maximal disjoint core
thickening, `n+2` bad scalars already at
`23/48-1/(24*2^26)`.  The large-field domain, literal event count, strict
prize-mass inequality, and operational `mcaDeltaStar` upper bound are now
kernel checked.  See
`docs/kb/deltastar-466-rate-quarter-smooth-isolated-counterexample-2026-07-10.md`
for the construction.  The stronger common-factor amplifier reaches the
executable radius `43/96+1/(3n)`, but its final operational stack is still in
progress.  Neither upper construction computes the first bad lattice radius,
so the exact rate-quarter delta-star remains open.

Several prize-scale components are already kernel checked.
`_HalfPredecessorRateQuarterMu16Locator.lean` proves the universal affine
identity among the three cubic locator blocks.
`_P1RateQuarterScaleArithmetic.lean` proves the exact `m=2^26` cardinal
ledger, the `n+2` maximal-thickening count, the radius identity

```text
delta = 23/48 - 2/(3n),
```

and the large-field constants separating the three unsafe cosets from the
smooth subgroup.  `_P1RateQuarterScaleConstruction.lean`,
`_P1RateQuarterScaleBadCount.lean`, and `_P1RateQuarterScaleFinalConsumer.lean`
complete the domain, count, and operational threshold ledger.

`_RateQuarterNextLatticeFourCoreBarrier.lean` also proves that any
one-fresh improvement at the next agreement lattice forces a pair core larger
than the current `3m` locator block.  Three next-lattice cores already force
an intersection of size at least `3m+1`; four maximally thickened cores do the
same.  Thus a stronger counterconstruction needs a genuinely larger
split-locator relation rather than another copy of the cubic `mu_16` cell.

Finally, a cardinal-only no-eight signature cap is false.
`_HalfPredecessorRateQuarterKFourNoEightSignatureRefuted.lean` constructs 24
abstract signatures: two disjoint source-root triples, each paired with the
12 lines of the affine plane of order three as missed triples.  They satisfy
the exact pair condition

```text
2 + |T_i intersect T_j| <= |E_i union E_j|
```

but exceed sixteen.  This is not a Reed--Solomon realization; it proves that
the missing no-eight input must relate the root and missed signatures through
their degree-three polynomials, rather than through cardinalities alone.

The global `n=16`, `k=4` rate-quarter bound, and therefore the corresponding
exact delta-star pin, remain open.
