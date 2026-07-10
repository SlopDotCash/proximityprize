# Rate-quarter saturated predecessor reduction (2026-07-10)

## Status

The prospective matching lower bound now has two explicit, axiom-clean
interfaces: a structured-floor bound and a guarded favorable four-pencil
extraction.  Both are proved equivalent to the same uniform predecessor
bad-count target; neither is discharged.

The construction is bad at agreement threshold

```text
t = 592,794,965,
```

so the immediately smaller radius asks for agreement `t+1`.  A saturated
source core has size

```text
z = t-1 = 592,794,964,
6z = 53m-8,
n = 16m.
```

If every predecessor event can be assigned to one of four common-core
polynomial source pencils, the terminal count is closed:

1. there are at most four source pencils;
2. every event needs at least two fresh coordinates beyond its core;
3. fresh petals for distinct scalars in one pencil are disjoint;
4. four such pencils carry at most `n` labels in total.

The fourth step no longer needs a saturated lower bound on the core sizes.
This does **not** prove the predecessor lower bound: the guarded residual asks
only that a stack with more than `n` bad scalars admit a favorable four-pencil
cover satisfying the two-fresh cutoff.  Stacks already within budget require
no cover.  The guarded proposition is logically equivalent to the uniform
count target, so it is a geometric proof interface rather than a weaker global
claim.

## 1. Integral five-core barrier

For five subsets `S_i` of an `n`-point universe, let `s_x` be the number of
sets containing coordinate `x`.  The integer inequality

```text
5 s_x <= s_x^2 + 6
```

is exact at multiplicities two and three.  Summing it and using the exact
first/second-moment identities gives

```text
4 sum_i |S_i| <= 6n + 20 lambda
```

when every distinct pair intersects in at most `lambda`.  Therefore five
cores of size at least `z` satisfy

```text
20z <= 6n + 20lambda.
```

At the saturated endpoint, `lambda=4m-2`; substituting `n=16m` and
`6z=53m-8` contradicts this inequality for `m>10`.  In a primitive collapsed
polynomial cluster, the factor root bound supplies exactly the pair cap.

The kernel theorems are

```text
fiveCore_integral_johnson
exists_pair_inter_card_ge_four_mul_sub_one_of_five
not_five_saturated_cores_in_primitive_cluster
```

in

```text
Frontier/_RateQuarterSaturatedFiveCoreBarrier.lean.
```

This improves the earlier quadratic Plotkin conclusion from at most five
source lines to at most four.  It is independent of the `mu_16` locator
pattern.

## 2. Four-cluster two-fresh capacity

For one source pencil with common core `D`, the existing line-core packing
theorem gives

```text
|Gamma| * max(1, T-|D|) + |D| <= n.
```

If a source core satisfies only `|D|+2<=T`, the exact packing law sharpens to

```text
2|Gamma| <= n-T+2.
```

At the P1 predecessor, four such clusters therefore satisfy

```text
2 * (n-T+2) <= n,
sum_i |Gamma_i| <= n.
```

This is formalized by

```text
two_mul_label_card_le_complement_add_two
fourTwoFreshCluster_label_card_le_universe
fourCluster_label_card_le_universe
saturated_core_ge_half
fourSaturatedCluster_label_card_le
```

in

```text
Frontier/_RateQuarterPredecessorFourClusterCapacity.lean.
```

## 3. Exact remaining structural target

For a bad scalar `gamma` with decoded polynomial `q_gamma`, view

```text
z_gamma = (1, gamma, coefficients(q_gamma))
```

as the normal of a hyperplane containing the lifted coordinate rows

```text
ell_x = (-u0(x), -u1(x), 1, x, ..., x^(k-1)).
```

Nonjointness and a witness of size at least `k` make this normal unique.
Two events sharing at least `k` coordinates determine a polynomial source
line.  The live geometric task is a rich-hyperplane/source-pencil decomposition
showing that any stack with more than `n` predecessor events admits a favorable
choice of decoded witnesses covered by four source pencils, each satisfying
`core.card+2<=T`.  `_RateQuarterPredecessorFourPencilReduction.lean` turns such
a cover into the literal `mcaBadCount<=n` result.

The alternative near-direction interface is
`PredecessorStructuredFloorResidual canonicalDomain`; its far branch is
already discharged.  `_P1RateQuarterPredecessorResidualEquiv.lean` proves that
this structured residual and `CanonicalLargeBadFourPencilExtraction` are both
equivalent to the uniform count target.  The reverse implications use the
absence of an over-budget stack and do not construct geometry.  Consequently
the exact advertised pin is still conditional under either interface, and the
unconditional lower bound remains `3/8`.

## 4. Projective structured reduction

Projective row-mix invariance makes the one-sided structured residual smaller.
The exact far count is `909,522,485`; adding the one projective point outside
an affine chart gives `909,522,486<n`.  Therefore any stack with more than `n`
predecessor bad scalars has both of the following properties:

1. its two rows are linearly independent modulo the Reed--Solomon code;
2. every nonzero projective combination `a*u0+b*u1` agrees with some codeword
   on at least `327,272,221` coordinates.

Equivalently, every such combination has a coset representative supported on
at most `746,469,603` coordinates.  This is formalized, without a new
assumption, by

```text
projectivelyStructuredRankTwo_of_N_lt_badCount
projectivelyNear_exists_support_le
predecessorStructuredFloorResidual_of_projectivelyStructured
```

in

```text
Frontier/_P1RateQuarterProjectiveStructuredSplit.lean.
```

The remaining residual is thus a genuine rank-two quotient pencil all of
whose projective points are near the code, rather than an arbitrary stack
whose direction row alone is near.

## 5. Extreme-zero branch closed through support 55,920,000

Translate a near direction by its witnessing codeword.  On a zero-safe line,
an appearing codeword with zero-agreement count `A` contributes at most

```text
support / (T-A)
```

scalars.  A clean simplex Johnson bound controls the cumulative codeword lists
around the offset.  Splitting at agreement deficiency `2,072,000` gives, for
support at most `55,920,000`,

```text
high-list cap = 18,
all-list cap  = 264,793,
support / (2,072,000+1) = 26,
18*55,920,000 + 264,793*26 = 1,013,444,618 < n.
```

Hence the zero-safe translated branch is unconditionally within budget when
the direction has at least `1,017,821,824` zeros.  The declarations

```text
puncturedZeroStratifiedLineWeight_le_twoTierJohnson
predecessor_lineBadScalars_card_le_N_of_support_le_twoTier
predecessor_mcaEvent_filter_card_le_N_of_support_le_twoTier
```

are in

```text
Frontier/_P1RateQuarterExtremeZeroJohnsonBand.lean.
```

This closes only the extreme endpoint of the projectively-near band; the
general support cap `746,469,603` is much larger.

The sharper affine total `1,013,444,618` leaves enough slack to pay for the
single projective point outside any affine chart:

```text
1,013,444,618 + 1 < n.
```

Consequently every invertible row mix of a hypothetical over-budget stack has
the following codeword-translated direction dichotomy:

```text
support > 55,920,000
or
zero-direction unsafe.
```

The unsafe alternative is unpacked rather than hidden.  It supplies a
threshold-size set on which a codeword explains the mixed offset and the
chosen direction codeword explains the mixed direction; invertibility
transports the same set to a `pairJointAgreesOn` witness for the original rows.
This arbitrary-chart statement is formalized by

```text
support_gt_twoTierCap_or_zeroDirectionUnsafe_of_N_lt_badCount_rowMix
support_gt_twoTierCap_or_transported_jointAgreement_of_N_lt_badCount_rowMix
```

in `Frontier/_P1RateQuarterProjectiveExtremeZeroSplit.lean`.  It does not
close the large-support alternative.

## 6. Four refuted shortcuts and the surviving global residual

The raw two-row interleaved collapse queries agreement
`2T-n=111,848,108`.  Its numerator fits the prize budget exactly when its
uniform interleaved-list cap satisfies `L<=1`.  A degree-`111,848,108`
vanishing polynomial gives two distinct list members at the zero stack, so
that premise is false for every injective P1 domain.  See
`_P1RateQuarterInterleavedCollapseNoGo.lean`.

The joint witness supplied by the projective zero-unsafe branch can be used
more efficiently than this raw all-stack list.  Ordinary exact-diagonal
Johnson bounds the predecessor threshold joint-pair list by `5`.  For any one
known threshold-size joint-agreement set, every MCA event has an escape
coordinate outside it.  If the bad family has more than `n` members, then any
choice of those coordinates has a fiber containing at least three scalars:

```text
n - T = 480,946,858,
2(n - T) < n < 3(n - T),
5(n - T) = 2,404,734,290.
```

Thus the fixed-witness branch is reduced to RS-specific control of three MCA
witnesses sharing one fresh coordinate.  Injectivity cannot be inferred from
the abstract event clauses: `_P1RateQuarterJointWitnessCharge.lean` gives a
two-coordinate `F_3` arbitrary-set-code example with two bad scalars and only
one possible escape coordinate.  This refutes only the bare charging step,
not the predecessor cap.  The stronger generic-RS exclusion is false as
well: `_RateQuarterSharedFreshCoordinateCounterexampleF11.lean` gives a
kernel-checked `RS[8,2]` code over `F_11` with three distinct half-radius
MCA-bad scalars whose witnesses share one coordinate outside the maximal
joint-agreement set of a known pair.  The example has rate `1/4` but not the
P1 length or threshold, so the live target is specifically P1-scale control,
not a code-agnostic or rate-only triple-impossibility lemma.  Its executable
certificate is `scripts/probes/probe_rate_quarter_p1_shared_fresh_coordinate.py`.

`_P1RateQuarterSharedFreshCoordinate.lean` isolates the forced local
structure.  Two distinct witness scalars give a codeword pencil jointly
agreeing on their witness intersection, and the witness sets are incomparable.
An intersection with the known joint set of size at least `K` absorbs that
pencil into the known pair, but the P1 counts do not force the premise.  If
three witness codewords are collinear, their common pencil agrees on the full
two-cover region, whose exact floor is `352,321,537 >= K`; this is still below
the event threshold `T`, so it is not a contradiction.

The same module introduced the sufficient proposition `SharedFreshTripleFree`
and proved `badFamily_card_le_N_of_sharedFreshTripleFree`.  That proposition is
now refuted even at literal P1.  `_P1RateQuarterSharedFreshTripleRefuted.lean`
uses a root-product pair on a threshold initial segment and zero rows on its
complement to construct `N-T+1=480,946,859` distinct bad scalars through one
fixed fresh coordinate, for every injective P1 domain.  The conditional
consumer remains valid, but its premise cannot close the branch.

The correct collinear statement is global rather than triple-local.
`_P1RateQuarterCollinearMismatchCharge.lean` proves that a whole selected
family lying on one fixed codeword pencil charges injectively to coordinates
where that pencil mismatches the received pair, hence has size at most `N`.
The surviving fixed-witness work is therefore genuinely non-collinear and
simultaneous; local shared-fresh exclusion is not a valid residual.

The improved BCHKS25 Guruswami--Sudan/Hensel architecture also remains far
above the prize coefficient.  Exact optimization of its integer interpolation
cells and Equation (13) lowers the printed threshold to

```text
11,510,231,640,868 bad scalars to fire,
```

so the contrapositive cap is `11,510,231,640,867`, strictly between
`10,719*n` and `10,720*n`.  The predecessor supplies only the `n+1` trigger.
This is an exact barrier for that universal rank-nullity architecture, not a
counterexample to the desired `n` cap; see
`deltastar-466-rate-quarter-bchks25-eq13-exact-barrier-2026-07-10.md`.

Pure set/source-line incidence is also insufficient.  A literal-P1
probabilistic construction has `n+1` abstract events while satisfying the
current size, pair-core, triple-root, petal, and source-line constraints.  The
missing condition is simultaneous Reed--Solomon realizability: all incident
decoded polynomial values must be affine in the scalar label at every
coordinate.  For the specific consecutive labels `gamma_i=i`, the resulting
support-dependent divided-difference/Vandermonde operator has full quotient
rank in the deterministic `N=64` probe over three smooth fields.  This is
computational evidence, not a label-uniform or universal theorem; see
`deltastar-466-rate-quarter-abstract-incidence-rank-barrier-2026-07-10.md`.

The corresponding algebraic reduction is now formal rather than only a matrix
proposal.  `Frontier/_SupportDividedDifferenceOperator.lean` defines the
support-indexed linear map and proves that supported decoded families and
global polynomial pencils lie in its kernel.  Its first unrestricted rank
interface is too strong: on a finite domain, the degree-`n` polynomial
vanishing on every evaluation point can be inserted in any non-anchor
component.  Thus `AnchoredKernelRigid` is false whenever a third label exists,
independently of the supports.

The companion
`Frontier/_SupportDividedDifferenceUnrestrictedKernelRefuted.lean` proves this
counterexample and replaces the target by `DegreeAnchoredKernelRigid`, which
restricts every component to the actual decoded degree bound.  Under that
corrected hypothesis, incidence at least two and injective labels force one
global polynomial pencil and hence joint Reed--Solomon agreement.  The P1 rank
probe already uses exactly this degree-`<K` source; proving its uniform
degree-restricted rigidity remains open.

Two unconditional consumers narrow that rank target.  If one anchor pair is
jointly incident with every label on at least `K` coordinates,
`degreeAnchoredKernelRigid_of_commonAnchorCoverage` closes the kernel by the
ordinary root bound.  More generally,
`degreeAnchoredKernelRigid_of_coordinateBootstrap` permits the two
already-vanishing parents to vary with the coordinate, provided they have
lower rank.  The remaining combinatorial task is to extract such a coverage
ordering, or a suitable coupled-core certificate, from every hypothetical
over-budget P1 support family.

In the deterministic `N=64` rank witness, the selected minor admits an exact
leaf/core decomposition: 45 label blocks peel as disjoint `16 x 16`
Vandermonde blocks, leaving an 18-label `288 x 288` core.  Its determinant is
algebraically independent of every peeled label.  This validates the
coordinate-bootstrap mechanism on the leaf portion but leaves a coupled core
rank problem.  Indeed 29 tested distinct-label substitutions make that fixed
minor singular, although the full operator remains rank `1008` after fallback
elimination in every case.  The result remains evidence for one support
family, not a P1 theorem.
