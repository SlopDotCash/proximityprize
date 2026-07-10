# Delta-star rate quarter: common-factor ownership amplifier (2026-07-10)

## Status

The maximally thickened smooth rate-quarter construction admits a second,
much larger amplification.  At the first prize prime `P1`, an exact compressed
certificate now gives `n+2` nonjoint bad scalars at agreement threshold

```text
t = 592,794,965 = (53m-2)/6,
n-t = 480,946,859 = (43m+2)/6,
```

where

```text
m = 2^26,
n = 16m = 2^30,
k = 4m = 2^28.
```

Thus the certified bad radius is

```text
delta_bad = (n-t)/n = 43/96 + 1/(3n).
```

The general amplifier arithmetic, polynomial identities, degree bounds,
root preservation, fresh-witness identity, scaled-hole agreement, nonjointness,
Möbius injectivity, and one-hole finite-field avoidance are kernel checked in

```text
Frontier/_RateQuarterCommonFactorOwnershipAmplifier.lean.
```

The actual P1 threshold/radius arithmetic and all six unsafe-coset
identifiers are kernel checked in

```text
Frontier/_P1RateQuarterCommonFactorArithmetic.lean.
```

An independent executable check is

```text
scripts/probes/probe_rate_quarter_common_factor_trade.py.
```

The full composition is kernel checked.  `_P1RateQuarterCommonFactorBadCount.lean`
proves the literal `n+2` event count and operational upper ledger on the
fibre-indexed code; `_P1RateQuarterCommonFactorCanonicalBridge.lean` transports it
to the literal prize code and proves
`mcaDeltaStar <= 43/96+1/(3n) < 1/2`.  This is an unconditional upper bound,
not an exact pin; it does not supply the matching predecessor lower bound.

### Discovery chain now formalized

The amplifier emerged from a sequence of exact obstructions rather than an
unguarded construction guess.

* `_RateQuarterNextLatticeFourCoreBarrier.lean` proves that three next-lattice
  one-fresh cores force a pair intersection at least `3m+1` by
  inclusion--exclusion.  It also proves by the sharp constant-weight Plotkin
  inequality that any four old-size cores force the same overlap once
  `r>=13`.
* `_RateQuarterNextLatticeSplitLocatorNecessity.lean` proves that such a pair
  intersection forces a monic split factor of degree at least `3m+1` in both
  decoded-line difference components, leaving quotient degree `<m`.  Three
  pair factorizations obey a polynomial-coefficient locator-cycle syzygy.  It
  explicitly does **not** infer constant-coefficient locator collinearity.
* `_RateQuarterNextLatticeOwnershipLedger.lean` proves the exact identity
  `B+A=n+2H`.  At the next core threshold, either one proper pair cell grows
  past `3m`, or the named `MultiHoleTripleTradeResidual` holds:
  `H>=2`, `H+2<=2A`, and `A<2H`.
* The same file red-teams the residual with the exact Venn-cell witness
  `H=A=2`, all proper pair cells `3m`, and all singleton cells `7r+1`.  This
  showed that no stronger cardinal-only argument could close the branch and
  directly suggested multiplying by a common quadratic while creating a
  second hole.  Iterating that trade gives the amplifier below.

## 1. Correction to the fixed-hole common-factor red team

An earlier red team correctly observed that adding a common root while keeping
the hole set fixed is harmful: an all-three coordinate is missed by no source
line and supplies no fresh label.

The mistaken extrapolation was that a common factor can never improve the
construction.  A coordinated trade changes both sides of the ledger.  If `H`
is the number of holes and `A` the all-three core size, then the exact
three-line one-fresh capacity is

```text
B = n + 2H - A.
```

Adding two dead common roots while adding one hole leaves `2H-A` unchanged.
This is the amplifier.

## 2. General `d`-step cell trade

Write `m=3r+1`.  After maximal private thickening, the smooth `mu_16` cell has

```text
holes                 1,
triple core           0,
proper pair cells     3m each,
singleton cells       7r+2 each,
core size             8m+r,
ownership budget      n+2.
```

For any admissible integer `d`:

1. select `d` singleton coordinates owned by line zero and `d` owned by line
   one;
2. let `G` be their monic degree-`2d` locator;
3. multiply every old line factor `f_i` by `G`;
4. set the received pair to zero on those `2d` roots, making them common to
   all three cores;
5. remove `d` singleton coordinates owned by line two and use them as new
   isolated holes.

The new cells are exactly

```text
H = d+1,
A = 2d,
proper pair cells = 3m each,
singleton cells = 7r+2-d each.
```

Hence

```text
universe size = (d+1)+2d+3(3m)+3(7r+2-d) = 16m,
core size     = (7r+2-d)+2(3m)+2d = 8m+r+d,
bad labels    = 3(7r+2-d)+3(3m)+3(d+1) = 16m+2.
```

These are the Lean theorems
`amplified_cell_universe_size_of_d_le`, `amplified_core_size`, and
`amplified_ownership_budget`.

## 3. Amplified polynomial lines

### Exact one-step architecture barrier

`_P1RateQuarterCommonFactorOneStepNoGo.lean` quantifies the final lattice gap over every possible
amplifier parameter `d0`, rather than only checking the concrete saturated choice.  It proves

```text
2*d0 + 1 < m  <->  d0 <= (m-2)/2
```

at the literal P1 scale, and therefore

```text
2*d0 + 1 < m
  -> 8*m+r+d0+1 < 592794966.
```

Conversely, making this architecture reach the predecessor threshold forces
`m <= 2*d0+1`, which overruns the degree budget.  Thus the missing agreement cannot be obtained by
choosing a larger common locator inside the existing `(X,1)` primitive-direction construction.
A successful direct predecessor counterexample must change the base proper-pair locator, primitive
direction, or ownership architecture; parameter thickening alone is exhausted.

The same file also proves that the primitive-direction tax is intrinsic to any factored polynomial
replacement.  For a projective direction `(A,B)`, the fresh label at `x` is
`-A(x)/B(x)`.  If two coordinates receive different labels—and hence in particular if the label
map is injective—then

```text
1 <= max (natDegree A) (natDegree B).
```

So merely replacing `(X,1)` by another polynomial direction cannot reclaim its one degree while
retaining distinct safe-coordinate labels.  A successful construction must instead alter the
factorization/ownership mechanism itself or tolerate and control label collisions.

There is a uniquely tight attempted escape.  Take `2d+1` common roots and retain `d+1` holes.  Its
formal ownership and core ledgers are exactly

```text
nominal charged labels = N+1,
agreement threshold    = 592794966.
```

So this would directly refute the predecessor residual.  The new no-go file proves why it cannot
work in the factored architecture: the degree inequality

```text
3*m + (2*d+1) + directionDegree < k
```

forces `directionDegree=0`.  A constant projective direction gives the same fresh label at every
safe coordinate, whereas two distinct labels already force direction degree at least one.  The
nominal endpoint has only one scalar of excess, and the exact ledger proves that one collision
drops `N+1` back to `N`.  Thus the last-step obstruction is a sharp trilemma: retain the degree
bound, retain injective labels, or reach the predecessor—this factored architecture can satisfy at
most two.

Nor can the missing degree be recovered by merely lowering the old source-factor degrees while
preserving the proper-pair cells.  The generic theorem
`three_mul_m_le_max_source_natDegree` proves that two distinct factors agreeing on an injectively
evaluated `3m`-coordinate block satisfy

```text
3*m <= max (natDegree f) (natDegree g).
```

This is the sharp polynomial root count for each proper-pair block.  Accordingly both terms in the
degree ledger are structural: the base factors pay `3m` for their pair block, and an injective
projective direction pays at least one more degree.  Coefficient changes within the same
three-source factorization cannot free either term.

The combined theorem `factored_odd_endpoint_not_degree_lt_k` packages the complete wall.  For
arbitrary source factors `f,g` and arbitrary projective direction `A,B`, the conjunction of

* a `3m`-coordinate proper-pair block for distinct `f,g`,
* the `2d+1` common roots needed at the predecessor, and
* merely two distinct projective fresh labels

forces

```text
k <= max(deg f,deg g) + (2*d+1) + max(deg A,deg B).
```

Hence the factored odd-root endpoint cannot satisfy a strict degree-`<k` budget.  This is no longer
a statement about the concrete locator coefficients or the particular direction `(X,1)`; it rules
out the whole three-source factored template with those exact block sizes.

### Saturation forces an affine locator triangle

The remaining non-factored three-line escape can also be normalized sharply at the exact endpoint.
`eq_C_mul_domainRootProduct_of_saturated_roots` proves that any polynomial of degree `<K` with
exactly `K-1` prescribed distinct roots is a scalar multiple of their monic root product.  Applying
this to the three cyclic line differences gives

```text
c12 * L12 + c23 * L23 + c31 * L31 = 0
```

with scalar—not polynomial—coefficients.  This is formalized by
`saturated_pair_cycle_forces_affine_locator_triangle`.

This strengthens the general split-locator necessity lane at the saturated endpoint: its
positive-degree quotient syzygy collapses to the precise affine locator-triangle interface studied
by the `mu_32` and `mu_64` P1 obstruction files.  Thus arbitrary coefficient choices in three
degree-`<K` polynomial lines do not evade the locator obstruction once each pair difference uses
the full `K-1` root budget.

The strengthened theorem
`saturated_pair_cycle_forces_nondegenerate_affine_locator_triangle` assumes the three source
factors are pairwise distinct and proves `c12,c23,c31` are all nonzero.  Consequently the exported
triangle is genuinely three-term; it cannot satisfy the interface through a zero coefficient or a
coincident source line.

Finally, `cancel_common_root_block_from_affine_locator_triangle` handles the normalization needed
by the dyadic obstruction.  If each saturated root set decomposes as a disjoint union

```text
common block C  union  proper pair block Pij,
```

then its locator factors as `L(C)*L(Pij)`.  The common monic locator is nonzero and cancels from the
three-term affine relation, yielding

```text
c12*L(P12) + c23*L(P23) + c31*L(P31) = 0.
```

Thus the output is now exactly a nondegenerate affine triangle among the disjoint proper-pair
locators, with the shared common-root block removed.

`affine_combination_of_monic_triangle` then converts the homogeneous relation into the normalized
form used by coefficient-minor tests.  For equal-degree monic `P,Q,R`, a relation with nonzero
`R`-coefficient yields scalars `alpha,beta` such that

```text
alpha + beta = 1,
R = alpha*P + beta*Q.
```

The weight-sum identity is forced by the common leading coefficient `1`; it is not an additional
hypothesis.  The bridge therefore reaches the literal affine-collinearity formulation without a
projective normalization gap.

The final adapter `coefficient_minors_vanish_of_monic_triangle` converts this affine relation into
the executable obstruction format.  For every pair of coefficient indices `i,j`, it proves

```text
(R_i-P_i)*(Q_j-P_j) - (R_j-P_j)*(Q_i-P_i) = 0.
```

These are precisely the anchored `2 x 2` minors used by finite locator censuses and norm-lift
arguments.  The chain from a saturated three-line predecessor architecture to coefficient-minor
vanishing is therefore fully kernel checked.

There is also a rigidity payoff beyond the minor interface.  Two distinct equal-degree monic
locators are linearly independent, so three locators on an affine line have a one-dimensional
space of scalar relations.  The theorems

```text
monic_same_degree_pair_linear_independent
affine_locator_relation_coefficients_unique
affine_locator_relation_space_one_dimensional
```

prove that any two coefficient triples annihilating the same locator triangle are proportional.
The theorem `saturated_two_component_lines_have_constant_projective_direction` performs that
application explicitly: from both component factorizations it produces `t` for which

```text
B1 - t*A1 = B2 - t*A2 = B3 - t*A3.
```

Thus an arbitrary saturated three-line polynomial-pair construction cannot use two independent
component syzygies; it collapses to a single constant projective direction.  Turning this collapse
into the full predecessor bad-scalar cap still requires an event-counting argument for that
constant-direction branch, so it is not yet claimed as the exact pin.

The normalization corollary
`saturated_two_component_lines_normalize_to_common_second_component` packages the next handoff.  It
produces `t,H` with

```text
B1-t*A1 = B2-t*A2 = B3-t*A3 = H.
```

Hence the invertible row operation `B ↦ B-tA`, followed by translation by the common codeword `H`,
puts all three source lines into zero-second-component form.  The remaining task is now sharply
localized: connect this normalized saturated branch to the existing projective extreme-zero
bad-count machinery, rather than proving a new locator theorem.

That quantitative connection is now proved.  Exact three-set inclusion--exclusion gives, for
three cores of size at least `592794965`, pair intersections at most `K-1`, and triple intersection
at least `2d+1`,

```text
|S1 union S2 union S3| >= 1,040,187,393
                         > 1,017,821,824.
```

The latter number is exactly the two-tier extreme-zero threshold `N-55,920,000`.
`saturated_three_cores_force_twoTier_direction_zero_set` proves that when the normalized direction
vanishes on the three cores, its zero set has cardinality at least `1,017,821,824`.  Therefore its
support is within the already-proved two-tier Johnson cap.  The safe normalized branch is ready for
the existing theorem `predecessor_mcaEvent_filter_card_le_N_of_zero_card_ge_twoTier`.

The MCA-facing theorem
`predecessor_mcaEvent_filter_card_le_N_of_saturated_three_zero_cores` now performs that invocation
directly and concludes that the predecessor event-filter cardinality is at most `N`.  Thus the
zero-direction-safe normalized saturated three-core branch is closed end to end.  The only logical
alternative is zero-direction unsafety, which the projective extreme-zero split turns into a
threshold-size joint explanation.

The unsafe alternative is now eliminated directly under the natural nonjoint hypothesis.
`zeroDirectionSafeLine_of_no_threshold_pairJointAgreement` proves that an unsafe codeword, paired
with the zero codeword, would jointly explain the two rows on its threshold-size zero-direction
agreement set.  Therefore no threshold joint explanation implies safety.  The assembled theorem

```text
predecessor_mcaEvent_filter_card_le_N_of_nonjoint_saturated_three_zero_cores
```

concludes the literal `<= N` predecessor event count from the saturated three-core geometry and
nonjointness alone.  This branch is closed; it is no longer a conditional handoff to either the
safe or unsafe extreme-zero subcase.

For extraction work, the hypotheses are bundled as
`NonjointSaturatedThreeZeroCoreCertificate`.  Its direct consumer

```text
mcaBadCount_le_N_of_nonjointSaturatedThreeZeroCoreCertificate
```

returns the canonical `mcaBadCount <= N` statement for the stack.  This gives other lanes a compact
alternative terminal certificate: they need only construct the three normalized cores and their
cardinality/intersection data, without importing the locator, normalization, or Johnson proof
chain.

The extraction interface is also projectively invariant.  A
`ProjectiveNonjointSaturatedThreeZeroCoreCertificate` contains an arbitrary invertible row chart and
a Reed--Solomon codeword subtracted from the mixed direction, with the three-core certificate stated
on those normalized rows.  Its consumer

```text
mcaBadCount_lt_N_of_projectiveNonjointSaturatedThreeZeroCoreCertificate
```

transports through both operations and proves the **original** stack has bad count strictly below
`N`.  The sharper two-tier closed budget absorbs the one affine slot potentially lost by moving
through a projective chart.  Extraction lanes therefore need not normalize their input stack in
advance or prove exact affine-count invariance themselves.

Finally, `CanonicalLargeBadProjectiveSaturatedThreeCoreExtraction` promotes the certificate to a
single global extraction residual: every allegedly over-budget canonical stack must emit such a
projective certificate.  Since the certificate consumer proves the same stack is actually below
`N`, the residual yields the uniform predecessor count.  The file wires this through the existing
structured-floor and adjacent-lattice connectors and proves

```text
canonical_mcaDeltaStar_eq_common_delta_of_projectiveSaturatedExtraction
```

namely exact equality at `43/96 + 1/(3N)` under this one new extraction hypothesis.  All analytic,
transport, endpoint, and upper-construction work is discharged; the only remaining content of this
route is producing the projective saturated-three-core certificate from an arbitrary over-budget
canonical stack.

### Logical-strength audit

The global guarded extraction residual is **not** claimed to be logically weaker than the original
predecessor target.  The theorem

```text
canonicalLargeBadProjectiveSaturatedExtraction_iff_uniform_badCount
```

proves they are equivalent.  Forward, the emitted certificate contradicts the over-budget guard.
Reverse, a uniform bound makes that guard false, so extraction holds vacuously and constructs no
cores.  This is the same logical phenomenon as the guarded four-pencil interface.  The value of the
new lane is its concrete local terminal certificate and its fully discharged consumer; genuine
remaining work is a nonvacuous geometric derivation under an assumed over-budget stack.

For direct downstream citation, the endpoint is also exported on the literal prize code as

```text
evalCode_mcaDeltaStar_eq_advertised_of_projectiveSaturatedExtraction
```

with conclusion `mcaDeltaStar (evalCode g N (k-1)) 2^-128 = 43/96 + 1/(3N)`.

The old universal cell uses factors

```text
f_0 = 0,
f_1 = (1-lambda) p_A(X^m),
f_2 = p_C(X^m),
```

whose three pair differences have disjoint `3m`-point split root sets.  Put

```text
h_i = G f_i,
c_i = (X h_i, h_i).
```

At a root of `G`, all three pairs evaluate to `(0,0)`.  Away from `G`, equality
of two amplified lines is equivalent to equality of the corresponding old
factor values.  Therefore amplification adds exactly the selected common
roots and preserves all three old proper pair blocks; it creates no accidental
pair roots.  This is kernel checked by
`amplifiedLine_eval_eq_zero_of_common_root` and
`amplifiedLine_eval_eq_iff_factor_eval_eq`.

At any nondead covered coordinate `x`, choose a source line missing `x` and
use

```text
gamma = -x,
q(X) = h_i(X)(X-x).
```

The polynomial identity

```text
q = (X h_i) + gamma h_i
```

is `amplifiedFreshWitness_eq_affineLine`; `q(x)=0` is also checked.  Thus all
nondead owned coordinates give distinct labels inside `mu_n`.

If `deg G=2d`, then the line intercept and fresh witness have degree at most

```text
3m+2d+1.
```

They remain degree `<k=4m` whenever `2d+1<m`.  At the saturated choice

```text
d_max = (m-2)/2 = 33,554,431,
```

the degree is exactly `4m-1`.  The Lean endpoint identities are
`saturated_d_degree_and_cell_available`, `saturated_threshold_identity`, and
`saturated_error_identity`.

## 4. Scaled-hole cancellation

At a hole coordinate `x`, write

```text
ell = G(x) != 0,
t_i = f_i(x),
h_i(x) = ell*t_i.
```

If the received pair is `(alpha*x,beta)`, the isolated scalar is

```text
gamma_i = x (ell*t_i-alpha)/(beta-ell*t_i).
```

Choose quotient-fibre row parameters `alpha_0,beta_0` and scale the received
row by `ell`:

```text
alpha = ell*alpha_0,
beta  = ell*beta_0.
```

Then the common factor cancels exactly:

```text
gamma_i = x (t_i-alpha_0)/(beta_0-t_i).
```

This is `scaledHoleGamma_scaled_rows`.  Its agreement and genuine nonjointness
corollaries are `scaledHoleGamma_scaled_rows_agreement` and
`scaledHole_scaled_received_pair_ne_line`.

The more general Möbius theorem `eq_of_scaledHoleGamma_eq` says that distinct
old values `t_i` give distinct labels whenever `x`, `ell`, and
`beta-alpha` are nonzero and the denominators are nonzero.

There is also a kernel-checked avoidance fallback.  Given any forbidden set
`B` of scalars, `exists_scaledHole_parameters_avoiding` chooses a hole row
whose three labels are distinct and avoid `B` under the sharp elementary
conditions

```text
3 < |F|,
3|B|+1 < |F|.
```

For fixed `beta`, each forbidden target excludes exactly one `alpha` on each
of the three lines.  This makes sequential global hole-label selection
available even without multiplicative coset symmetry.

## 5. Compressed saturated P1 certificate

The maximum construction does not enumerate `33,554,431` roots or holes.
It uses quotient fibres:

```text
common roots: first d_max points of private fibre 4  (line 0),
              first d_max points of private fibre 11 (line 1),
new holes:    first d_max points of private fibre 13 (line 2),
old hole:     the residual point in fibre 15.
```

All three old factor values are distinct on fibres `4,11,13,15`, and
`d_max<m`, so every chosen cell is available.  The common-root and hole fibres
are disjoint, hence `G` is nonzero on every hole.

For both hole fibres the probe finds the tiny scaled-row choice

```text
alpha_0 = 1,
beta_0  = 2.
```

On fibre 13, the three exact coset constants are

```text
182687704666362864775460604089535377560070782976,
357427157257065199771064609774836810806559371356,
 48131014922838568432685688908340148811467554291.
```

The probe verifies:

* every constant has nonunit `n`th power, so its whole label coset is outside
  `mu_n`;
* every pairwise constant ratio has nonunit `m`th power, so the three
  fibre-13 label cosets are disjoint;
* all nine ratios from the three residual fibre-15 labels to the three full
  fibre-13 cosets have nonunit `m`th power, so the old hole labels are also
  disjoint from every new label;
* the four quotient-fibre factor-value triples are nondegenerate where used;
* the exact core, threshold, radius, degree, and `n+2` count identities hold.

The final saturated ledger is

```text
d                  = 33,554,431,
holes              = 33,554,432,
triple core         = 67,108,862 = m-2,
proper pair each    = 201,326,592 = 3m,
core size           = 592,794,964,
agreement threshold = 592,794,965,
error count          = 480,946,859,
bad scalars          = 1,073,741,826 = n+2.
```

## 6. Red-team audit and remaining lower-bound work

The following possible failure modes were checked explicitly.

* **Dead common roots:** charged exactly by the `-A` term in `n+2H-A`; the
  simultaneous new holes pay for them.
* **Accidental pair roots:** ruled out away from `G` by cancellation of the
  nonzero common-locator value.
* **Degree overflow:** the saturated intercept and witness degree is `4m-1`,
  not `4m`.
* **Hole accidentally joining a core:** the scaled denominator
  `ell(beta_0-t_i)` is nonzero, so the received direction row differs from
  every decoded line.
* **Within-hole collision:** ruled out by Möbius injectivity.
* **Collision with safe labels:** all isolated cosets lie outside `mu_n`,
  whereas safe labels are `-x` with `x in mu_n`.
* **Cross-hole/cross-line collision:** certified by the exact `m`th-power
  tests described above.
* **Insufficient private coordinates:** `d_max<m`, while each selected
  private quotient fibre has size `m`.

Operational integration is complete.  What remains is goodness at the
immediately preceding lattice radius `480946858/n`.
`_P1RateQuarterPredecessorGenericSplit.lean` reduces this to
`PredecessorStructuredFloorResidual canonicalDomain`.
`_P1RateQuarterFourPencilExactPin.lean` gives an alternative conditional route
through guarded favorable four-pencil extraction with a two-fresh cutoff and
no saturated core-size lower bound.  The two global residual interfaces are
proved equivalent to the same uniform predecessor count in
`_P1RateQuarterPredecessorResidualEquiv.lean`.  Under either hypothesis the
adjacent-floor connector proves exact equality at `43/96+1/(3n)`.  Neither
hypothesis is proved here.

## 7. Multi-line frontier after saturation

`_RateQuarterSaturatedFiveCoreBarrier.lean` sharpens the earlier quadratic
six-core Plotkin cutoff using integer coordinate multiplicities.  For five
cores let `s_x` be the number containing coordinate `x`.  The pointwise law

```text
5 s_x <= s_x^2 + 6
```

and exact incidence double counting give

```text
20z <= 6n + 20lambda
```

when each core has size at least `z` and every pair intersection is at most
`lambda`.  Substituting `n=16m`, `lambda=4m-2`, and `6z=53m-8` is already
contradictory for `m>10`.  Inside a primitive collapsed cluster the factor
degree supplies precisely this pair cap, so the axiom-clean theorem
`not_five_saturated_cores_in_primitive_cluster` rules out five or more
saturated source lines.  Only clusters of at most four source lines remain;
this argument is independent of the particular `mu_16` locator pattern.
