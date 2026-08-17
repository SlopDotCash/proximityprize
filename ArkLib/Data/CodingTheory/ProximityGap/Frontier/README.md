# Proximity Gap — Frontier scratch lanes (historical #334 → #444 → #464 → #466; standalone #1)

Drop-in starting points for the actionable open targets. Each file:
- imports ONLY its minimal substrate (fast `lake env lean`, ~30s, no build lock),
- states the precise target as an honest named `Prop`/hypothesis (no `sorry`, no fake `axiom`),
- documents the reference + the in-tree substrate API to consume.

**Iterate:** `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/<File>.lean`
**Land:** one real `lake build <Module>` (autoImplicit=false) + axiom audit, then the push loop.
**Lane hygiene:** files starting `_` are scratch/lane files (most are git-tracked — treat them as
lane state, not throwaway); start a new lane from a nearby minimal file with the same substrate.
Read the parent `CLAUDE.md` (build/concurrency/honesty rules) before touching anything.

## Live targets (standalone refresh 2026-08-16)

**The current campaign is
[`elizaOS/proximityprize#1`](https://github.com/elizaOS/proximityprize/issues/1).** Historical
issue #466 names the predecessor campaign and remains useful provenance, but it is not the current
control plane. Read `docs/kb/deltastar-DOSSIER-v4-2026-08-16.md` first for the standalone status,
post-v3 evidence ledger, and issue map.

> **PRIMARY ENTRY POINT (rate-1/2 strip route, 2026-07-11):**
> `docs/kb/deltastar-466-one-question-map-2026-07-11.md` — THE one-question state. The whole SYZ arc
> has converged: the conditional δ* bracket now depends on exactly **three open Props**
> (`uniformSylvester` reduced to near-balance `ι ≤ 1`, with parity-corrected generator gap `≤ 2`
> for even total degree and `{1,3}` for odd total degree; `StripSyzygyControlledCeiling`; `hrank`),
> each a face of the **syzygy structure of the witness-support family `{Sᵢ} ⊂ μ_n`**, which
> SYZ49 identifies with the BGK level set. The entire μ-basis classical column beneath F1 is now
> proved (SYZ61→SYZ65). Read that map first, then the SYZ54+SYZ67 addenda in
> `docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` §6.

The detailed historical frontier (CORE Paley/BGK line) is
`docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` §6 and
`../PROXIMITY_PRIZE_WORKBENCH.lean` §5. Reconcile those lanes against dossier v4 before attacking
one; this README mostly records the accumulated historical lane files below.

**2026-07-10/11 state change — read dossier v3 §42 first.** The r=3 B-side rung is now the
lossless graded ladder `OffDiagQuadrupleBound ⟹ FourthMomentBound ⟹ DistStratumEnergyBound`
(lossless = `FullDFTFlat`; R297–R304, rungs m=3/6/9 discharged, all three ladder Props OPEN);
the P1 rate-quarter predecessor D-charge cone is COMPLETE with pin =
`SmallPoolClosure ∧ StallResidual` (heavy window closed, three architectures kernel-refuted,
two-cover window REALIZED); W15 safe branch closed at UD-plus (window
`LargeZeroSafeLineListBudgeted` open). Machine-checked convergence: both cones terminate at the
same beyond-Johnson wall. Bracket unchanged; core open. Full record:
`docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` §42.

**2026-07-11 follow-up — dossier v3 §43.** `SmallPoolClosure` DISCHARGED; P1 counting branch
reduced to the single Prop `SwarmResidual` (via `stallResidual_of_swarmResidual` +
`predecessorDelta_le_mcaDeltaStar_of_stall`; adversarial non-dyadic domains refute
StallResidual, the dyadic gap (2^27, 2^28) protects the literal μ_{2^30}). B-side: absolute-K
`FullDFTFlat` refuted (Gumbel log m); r=3 closed modulo `FullDFTFlatLog ∧ FourthMomentBound`
at (1+log m) loss. Bracket unchanged; core open.

**2026-07-11 constant-width Hall kernel.**
`_P1RateQuarterEightLabelHallKernel.lean` combines the sharp two-label singleton census with the
six-label bad-pair vertex cover.  For exactly `N+1` threshold witnesses there is one exceptional
set of cardinality at most eight such that every nonempty subset of its complement has projected
divided-difference budget at least `K` times its cardinality.  Thus any remaining failure of a
Hall-to-block-Vandermonde injectivity theorem is confined to eight labels; this is a localization,
not yet a discharge of `SwarmResidual` or an exact delta-star pin.
`_P1EightLabelHallToRigidityRefuted.lean` records the sharp limitation: an exact `F_7` system has
only two exceptional anchor labels and every complement subset satisfies the same Hall budgets,
but its degree-two anchored kernel is nontrivial.  Therefore the eight-label theorem cannot feed
a Hall-only local-to-global argument; a surviving producer must use the P1 event geometry or a
genuine maximal-recoverability/determinantal input.
`_P1EightLabelComplementForcedSecant.lean` supplies the first event-geometric successor: deleting
any eight labels from an `N+1` predecessor family still leaves two Hall-safe-complement witnesses
whose agreement sets overlap on at least `K` coordinates.  The constant-width kernel therefore
cannot quarantine the large-core geometry; the next live bridge is to iterate or cluster these
forced secants into the existing polynomial-pencil consumers.
`_P1EightLabelHallSafeSecantMatching.lean` performs that iteration using the established greedy
matching extractor: an over-budget family retains at least `2^29-6 = 536870906` vertex-disjoint
`K`-core secants after deletion of any eight labels.  For the Hall-kernel exceptional set, all
endpoints lie in the Hall-safe complement.  The live algebraic/geometric target is therefore
simultaneous consolidation of this half-billion-secants matching, not recovery from bare Hall
budgets.
`_P1HalfBillionCorePackingNoGo.lean` proves that matching size and core cardinality still do not
force consolidation: inside an `N=4K` coordinate domain it explicitly constructs `2K=2^29`
distinct `K`-cores, while every two distinct cores intersect in fewer than `K` coordinates.  This
is six more cores than the matching lower bound.  A successful consolidation theorem must use the
joint arithmetic of secant parameters and core locations; a second Plotkin/pigeonhole step on the
core set system is formally ruled out.
The same file now lifts every packed core through Lagrange interpolation: for any shared received
stack and any injective embedding of the `4K` coordinates into a field, each packed `K`-set is
contained in the literal joint core of a degree-`<K` polynomial line.  Thus individual polynomial
realizability also does not rescue the cardinality argument.  The remaining potentially positive
invariant is simultaneous control—distinctness of the interpolated secant parameters and absence
of extra core points under the actual decoded-family compatibility equations.
An explicit nodal companion in the same file proves that the packing index also supports `2K`
genuinely distinct degree-`<K` polynomial parameters: delete one base root and use either of two
distinct nonzero scalar weights.  This closes the separate parameter-count objection.  The two
constructions are not yet welded—the remaining exact question is whether one shared received
stack can simultaneously make those distinct nodal parameters agree on the prescribed packed
cores without creating the prize-forbidden structure.
That weld is now complete in `core_subset_jointCore_nodalLine`: one shared received stack supports
all `2K` distinct degree-`<K` nodal lines on their prescribed packed cores.  Consequently shared-
stack polynomial-line compatibility, core size, pairwise root caps, and half-billion matching
size together still do not consolidate the lines.  The surviving distinction from the prize
family is narrower: these abstract lines have not been proved to arise as canonical secants of
threshold-size decoded scalar witnesses satisfying the full MCA event clauses.
The canonical-secant algebra is now also discharged: two arbitrary scalar labels decoded by the
same nodal polynomial have canonical secant exactly `(nodalParameter,0)`.  Thus every packed line
has a literal two-witness secant realization.  The remaining gap is quantitatively exact rather
than structural: its guaranteed agreement is `K=2^28`, while a predecessor witness needs
`T=592794966`, a deficit of `T-K=324359510` coordinates.  Threshold amplification subject to the
five-set overlap forcing is the sole surviving obstruction for this construction.
`not_five_nodalLines_all_threshold` closes that amplification attempt end-to-end: among any five
distinct nodal canonical lines on the shared stack, at least one has joint core below `T`.  The
proof factors through a symbolic `(k,t)` integral-Johnson theorem and specializes axiom-cleanly at
P1.  Hence repeated-polynomial witness pairs cannot reach the predecessor threshold at scale;
any genuine over-budget family must use pairs with different decoded polynomials whose canonical
secant retains only the forced `K`-overlap, returning exactly to the live simultaneous-geometry
problem.
The pair-local side is now separated cleanly in `exists_threshold_pair_with_intersection_core`:
every packed `K`-core extends to two `T`-element agreement sets with intersection exactly that
core.  Their union has size `2T-K=917154476<N`, leaving `156587348` coordinates of slack.  Thus
one differing-polynomial secant has ample room to support two predecessor witnesses; the
obstruction is exclusively simultaneous compatibility across the half-billion matched pairs,
not the geometry or counting of one pair.
`_P1MatchedSecantInteractionGraph.lean` supplies the first quotient-level simultaneous law.
Pair-vertices interact when some cross-pair endpoint witnesses overlap on at least `K`
coordinates.  Any five vertex-disjoint matched pairs contain two distinct interacting vertices;
equivalently, the pair-interaction graph has independence number at most four.  This promotes the
sharp five-set forcing from scalar witnesses to the half-billion matched-secant population and
creates the correct graph for density and polynomial-line propagation arguments.
The file now packages this as `interactionGraph` for every finite endpoint-disjoint matching and
proves `interactionGraph_compl_cliqueFree_five`.  This is the reusable global statement: standard
four-part Turán extremal machinery may be applied directly to obtain a quadratic interaction
supply.  The remaining prize-specific step is to turn those cross-endpoint overlaps into equality
or bounded clustering of the original matched secant parameters.
Every interaction is now given an exact four-colour orientation socket by
`pairInteracts_iff_exists_orientation`; `interactionOrientation_spec` selects a canonical endpoint
pair and retains its `K`-overlap.  This removes disjunctive endpoint bookkeeping from the next
algebraic layer.  A finite interaction supply can therefore be split into four uniform cross-
secant formulas before applying determinant or polynomial-line propagation arguments.
`exists_four_interaction_centres` strengthens density to a bounded-star statement without any
edge enumeration: a maximum independent set has at most four pair-vertices and dominates the
entire matching.  Hence every other matched secant has a cross-endpoint `K`-overlap with one of
four centres.  This is now strikingly parallel to the four-pencil endpoint; what remains is the
algebraic propagation from an interaction with a centre to membership in a bounded family of
polynomial lines.
`exists_four_centres_with_oriented_routing` makes that residual deterministic: for every outside
matched pair it chooses a centre, an endpoint on the outside pair, and an endpoint on the centre,
and returns the literal `K`-overlap certificate for those witnesses.  The graph/existential layer
is therefore closed.  A next producer can consume four fixed centres and one uniform routed
cross-secant equation per outside pair, with no remaining choice or orientation bookkeeping.
`pairInteracts_exists_crossSecant_core` completes the decoded-family weld for one routed edge:
the selected cross endpoints determine their literal canonical polynomial secant, and its joint
core has cardinality at least `K`.  Thus the four-centre output is no longer merely a set-overlap
graph; it is a routed supply of large-core canonical cross-secants.  The remaining propagation
question is whether this star of cross-secants forces the outside pair's original secant into a
bounded polynomial-line cluster around its centre.
`_P1OneEndpointCentrePropagationRefuted.lean` proves that implication false at the algebraic
interface: fixing the routed endpoint and centre leaves the cross-secant unchanged while varying
the unseen partner changes the outside pair's original secant from `(0,0)` to `(0,1)`.  Hence the
four-centre star cannot cluster original lines from one-endpoint routing alone.  A viable successor
must route both endpoints to centres, force a second independent cross-equation, or exploit a
global decoded-family invariant coupling the unobserved partner.
`exists_eight_centres_dominating_both_endpoints` supplies exactly that repair.  Apply the sharp
five-set theorem separately to endpoint zero and endpoint one: each fixed-endpoint interaction
graph has four dominating centres, so their union has cardinality at most eight.  Outside this
union, both endpoints of every matched pair have same-oriented `K`-overlaps with centre endpoints.
The one-endpoint blindness is therefore removed at the cost of enlarging four centres to eight.
`_P1TwoEndpointCentreReconstruction.lean` closes the next algebraic target exactly.  Evaluating a
cross-secant at its outside scalar recovers that endpoint's decoded polynomial.  Therefore the two
same-oriented routed cross-secants (even when they use different centres) recover both outside
decoded polynomials and factor the original matched secant; the ordered pair of cross-secants is
injective in the outside lifted pair.  Reconstruction is no longer the residual.  The live P1
socket is a bounded-multiplicity theorem for large-`K` cross-secants through the sixteen centre
endpoints, or a global compatibility invariant that bounds the number of such reconstructed
ordered pairs.  The same file now audits the purely algebraic version of that socket and refutes
it sharply: for any fixed lifted centre and any polynomial slope `r`, evaluating the corresponding
centre-pencil line at an outside scalar produces a decoded polynomial whose canonical cross-secant
is literally that line.  Distinct slopes remain distinct, so one centre contains an injective copy
of the entire polynomial space.  Any multiplicity bound must therefore use the `K`-core incidence
condition (and likely simultaneous compatibility of those cores), not merely bounded centres,
degree-free secant algebra, or two-endpoint reconstruction.  The strengthened construction in
`_P1HalfBillionCorePackingNoGo.lean` now refutes even that single-centre `K`-core multiplicity
socket at production scale.  Use each of the `2K` distinct degree-`<K` nodal polynomials as a
slope `r_p`, set its intercept to `qDelta-C(delta)r_p`, and couple the first received coordinate
to the shared nodal slope word.  All `2K=2^29` lines then pass through the same lifted centre,
remain distinct and degree-`<K`, and simultaneously carry their prescribed `K`-point joint cores
against one received stack.  Thus neither bounded centres nor large-core incidence at one centre
can cluster the routed lines.  A surviving P1 proof must use compatibility between the two routed
centre pencils for each matched pair together with the original threshold-size endpoint witness
sets; treating either routed endpoint separately is now closed sharply.  The new
`nodalPencilLine_two_routes_and_original` closes the core-only coupled variant too: choose two
distinct outside scalars on one packed pencil line and route both to its common centre.  Both
cross-secants and the outside pair's original canonical secant are exactly that same line, while
the shared stack still supplies its `K`-core.  Hence two-route algebraic compatibility plus the
`K`-core condition is still insufficient.  The quantitatively larger `T`-element full-agreement
witness at each outside scalar is now the precise live ingredient; it cannot be discarded in
favor of secant cores alone.

**2026-07-11 part 2 — dossier v3 §44 (R307–R309 B-side close-out).** Absolute-C DIST rung from
a-averages (`distStratum_absoluteC_of_fourth_and_eighth`, lag endgame
`distStratum_absoluteC_of_offZeroLags`); moment stack ⟺ R27 tower
(`evenMoment_eq_iterConv_energy`). ⚠️ Corrections: R35/R144 budgets lump lag-0 (vacuous at
absolute constants); uniform `TwoCharacterWeilInput` contradicted at Θ(q). Remaining open
B-side input = one √m-saving Jacobi-angle cancellation (three equivalent two-input routes).
Bracket unchanged; core open.

**2026-07-11 part 3, session final — dossier v3 §45 (COMPLETE residual inventory).** Cross-cone
bridge: moment layers = one identity family, but the open layers are a calibrated NON-bridge
(`swarm_sub_burgess` — the "one wall" is class-level, not reduction-level); fiber-Chebyshev
u-relative hope refuted (F0 unmoved), codeword-pair (k−1) cap landed; junk-slice composition
no-improvement closes the P1 arc (11 rounds, 93 kernel theorems); W15 width-k gap closed —
sharp dichotomy L_near = 1 ⟺ 2n+k ≤ 3a (parts 1–6 complete). Residuals: B-side lag⟺moment⟺tower
pair + DIST rungs m ≥ 12; P1 `SwarmResidual`; W15 strip sliver / Λ ≤ 2 (empirical) / `hunsafe` /
`hfarL`. Bracket unchanged; core open.

## The BGK depth-ladder lane (2026-07-10)

**DC correction (2026-07-11).**  The later raw endpoint
`DepthSevenFlatnessResidual : E₇ ≤ 2¹⁸|G|⁷` is formally refuted at production: the mandatory
zero-frequency term gives `2⁴²⁰ ≤ qE₇`, while the raw residual and `q≤2¹⁵⁹` give
`qE₇≤2³⁸⁷`.  The live successor is the DC-subtracted residual

`qE₇ - |G|¹⁴ ≤ q·2¹⁸·|G|⁷`,

formalized with its full consumer in `_BGKDepthSevenFlatnessResidualRefuted.lean`.  Do not attack
the historical raw Prop in `_BGKDepthSevenFlatnessResidual.lean`.
`_BGKRenergyRepresentationBridge.lean` identifies the BGK lane-local energy with the standard
library energy and proves that standard `DCEnergyBound G 7` implies the repaired coefficient-`2^18`
residual, so the census and BGK lanes now share one exact centered object.

**Centered convolution collapse (2026-07-11).**
`_BGKCenteredConvolutionCollapse.lean` gives the repaired object an exact one-dimensional form.
If `f₆` is the six-fold additive representation function and
`C₆(δ)=Σ_d f₆(d)f₆(d+δ)`, multiplicative invariance gives

`qE₇-|G|¹⁴ = |G|·Σ_{u∈G}(qC₆(1-u)-|G|¹²)`.

Thus the live coefficient-`2^18` residual is equivalent to a **signed** average along `1-G`, not
a positive packet count.  At `|G|=2^30`, `q≤2^159`, the normalized sum has the explicit target
`Σ_{u∈G}(qC₆(1-u)-|G|¹²) ≤ 2^357`.  The centered autocorrelation has exact global mean zero, so
absolute-value or packet-positive envelopes destroy precisely the cancellation this formulation
exposes.  A primitive-character audit also proves that `|G|` times this signed sum is exactly
`Σ_{b≠0}|η_b|^14`; in particular the total sum is nonnegative.  The collapse is therefore a
structural one-dimensional rerouting of the off-zero moment, not a moment-method bypass.
`_BGKCenteredTranslatePDNoGo.lean` now draws the exact boundary of that rerouting.  Global mean
zero, additive positive semidefiniteness, and multiplicative invariance alone admit an unbounded
centered-delta scaling ray.  In the exact proper-subgroup cell `(p,n)=(13313,256)`, the centered
coefficient is `312012.706...>2^18`.  This does not touch the production prime; it proves that a
successful restriction theorem must use extra arithmetic specific to the production subgroup,
not only those three homogeneous properties.
`_BGKCenteredTranslateConeDuality.lean` makes this sharper directly in Fourier coordinates.  For
nonnegative zero-DC weights constant on multiplicative orbits, the restriction is exactly
`|G|^-1*sum_b w_b*|eta_b|^2`; at unit spectral mass its optimum is the worst normalized period
square, attained on one orbit.  Hence the universal Fourier-cone program is the Paley spectral
problem itself.  The actual autocorrelation has the extra nonlinear constraint
`w_b=|eta_b|^12`, but `_BGKLowerMomentOrbitSpikeNoGo.lean` proves that Parseval, orbit
multiplicity, the trivial pointwise cap, and even hypothetical Wick ceilings through the twelfth
moment still allow a fourteenth moment between `2^15` and `2^16` times the target.  A survivor
must control joint arithmetic of the complete period profile at depth seven.
`_BGKPeriodProfileArithmeticAudit.lean` restores several pieces of genuine period arithmetic.
Galois transitivity and the exact period-power congruence each exclude the literal rational
spike, but a nonzero integral, trace-correct profile still passes the Wick ceilings through depth
six and misses depth seven by 8--9 bits.  The 2026 Wu--Wang--Pan Jacobi determinant controls one
linear coefficient of the period polynomial; an irreducible monic integral family with fixed
trace, norm, and linear coefficient nevertheless has an arbitrarily large real root.  A useful
period theorem must therefore couple all ramified conjugates quantitatively, not merely add
integrality, one determinant, or one moment residue to the scalar cone.
The updated research control plane is the
[`10 x 10 centered attack matrix`](../../../../../docs/kb/deltastar-466-ten-by-ten-centered-attack-matrix-2026-07-11.md),
with the focused 2026 theorem screen in
[`depth-seven per-prime literature audit`](../../../../../docs/kb/deltastar-466-depth7-per-prime-literature-audit-2026-07-11.md).

**Weighted collision and Jacobi audit (2026-07-11).**
`_BGKWeightedCollisionMoment.lean` generalizes the Fourier/collision identity to arbitrary
integer coefficient patterns. In particular, the leading one-repeat partition is the exact
centered mixed moment
`sum_(b != 0) eta_(2b) eta_b^5 eta_(-b)^7`, giving the repeated-sector lane a concrete signed
socket rather than a positive union bound. `_AJT13CenteredMomentEquivalence.lean` closes a
different audit: the proposed 13-variable annihilator Jacobi tensor is exactly the centered
fourteenth moment after deleting the principal character. Its `m^7` bound is therefore an
equivalent dual-coordinate target, not an independent orthogonality saving.
`_AJT13CenteredBoundaryBridge.lean` then proves that a centered Wick-coefficient bound
(`13!!=135135`) absorbs the `1/m` translation inside the public coefficient `2^18` whenever
`m>=21`; the principal-character boundary is no longer a separate Wick-scale residual.
`_BGKRepeatedSectorNewtonAbsorption.lean` then expands the ordered-injective transform by Newton
identities.  Its exact Möbius masses begin `42,791,8820,...`, total `25401599`; the production
Hölder envelope is `137.8488...<138`, and a formal sublinear barrier splits the wrap allowance as
`126871+138=127009`.  `_BGKFourteenFactorYoung.lean` supplies the kernel-checked 14-factor
AM--GM and optimized-padding socket. `_BGKShiftedEtaPaddedHolder.lean` now closes the analytic
adapter for every `k<=13` shifted eta monomial: unit dilation, coefficients `1,...,7`, the exact
erased-frequency model, and the canonical padding scale are all formal.
`_BGKRepeatedNewtonFullEnumeration.lean` closes the finite and fixed-target seams: all 88 nonzero
monomials are checked by `ring`, their exact `B_2,...,B_13` masses are computed in the kernel,
every shifted term reaches the Holder adapter, and fixed integer padding `R=79880` proves the
whole repeated envelope at `F(T)` is below `138*q*n^7`.
`_BGKRepeatedEnvelopeSecantClosure.lean` closes the rest of the repeated cone: it identifies the
canonical root envelope with the literal real-power envelope, proves the above-target concave
secant has slope below `1/1024`, and provides the end-to-end field consumer
`productionSlackBarrier_of_actualEtaEnvelope`.  From the exact moment decomposition, the actual
eta-envelope recurrence, and only the injective `126871` allocation, that theorem forces the
public `127009` target.  No repeated-sector enumeration, dilation, scalar, monotonicity, secant,
or wiring theorem remains.  The sole principal depth-seven core is therefore the **signed
injective** packet defect at coefficient `126871`.

**Injective/exterior audit (2026-07-11).**
`_BGKDepthSevenInjectiveVarianceEquivalence.lean` identifies that core exactly with seven-subset
sum mixing:
`(7!)^2*sum_y(q*a_y-C(n,7))^2 <= 126871*q^2*n^7`.
`_BGKInjectiveFactorialCovarianceAudit.lean` records the normalization that every covariance
transfer must preserve.  If `A` is the unordered subset histogram, then the ordered-injective
profile is `J=7!*A`, so `V(J)=(7!)^2V(A)` with `(7!)^2=25401600`.  Its exact polarization gate
pairs `J`, not `A`, with the repeated-coordinate defect.  A genuine two-point group-sum profile
refutes the corresponding universal contraction, while leaving a production-specific signed
covariance theorem open.
This is a useful coordinate change, not a bypass. `_BGKSamplingWithoutReplacementNoGo.lean`
proves generic exterior coupling misses by over `141` energy bits and would leave a period bound
over `1835` times the Paley ceiling. `_BGKJohnsonKneserDepthSevenNoGo.lean` proves ordinary
one-sided Kneser mixing misses by `162--163` bits (two-sided mixing by `190--191`); even the
Johnson local-injectivity/Hoffman route misses by `163--164` bits.  The survivor must therefore
use subgroup-specific arithmetic cancellation, not phase norms or association-scheme expansion
alone. `_BGKJohnsonPhaseGradeNoGo.lean` strengthens this: a primitive-fourteenth-root phase
family has power sums `p_1,...,p_7=0` but still places three quarters of its norm in Johnson
grades `1,...,6`, with grade six alone carrying `7/16`.  Newton/Wick subtraction does not
universally isolate the top grade. `_BGKSevenSubsetOverlapDecomposition.lean` gives the exact
wraparound-compatible sunflower split
`W_7=sum_(r=0)^7 D_r*C(|G|-2r,7-r)`: cancelling a common core preserves the nonzero cyclotomic
lift marker.  Hence all overlap configurations are a weighted depth-`<=6` term and the coefficient
of the globally disjoint primitive depth-seven term is one.  Existing lower-depth packet results
do not yet bound that weighted census, so this is an exact localization rather than a discharge.
`_BGKSevenOverlapProductionBudget.lean` sharpens the boundary: `D_0=D_1=0`, but even an
optimistic termwise Wick cap for `D_2` costs coefficient `158760>126871`; the five completed
depths `2,...,6` total `2714355`, between 21 and 22 full injective allowances.  It also maps every
marked depth-two pair to the existing projective-accident socket.  Thus lower-depth structure
remains relevant, but positive completion counting cannot close the target without signed/DC
cancellation or a genuinely smaller subgroup-arithmetic census.  The same file proves that
accident-freeness, and hence the existing `kappa_n(x)=(x-1)^n` difference-signature injectivity
condition modulo inversion, annihilates `D_2`; both production-prime consumers are formal, but
their `n=2^30` injectivity hypothesis is still open.
`_ANT46KappaProductionReduction.lean` gives that hypothesis two exact certificate forms.  On an
inversion transversal it is equivalent to nonvanishing of one ordered discriminant times the
self-class value; the literal production polynomial has degree `536870911` and Sylvester order
`1073741821`.  Prime-factor projection reduces the first and second primes to separation in
certified 59-bit and 67-bit prime-order groups, respectively.  Those projection adapters remove
small cofactor components, but the projected injectivity itself remains an open power-residue
separation problem.
`_ANT46ProjectedCharacterNoGo.lean` audits that last projection.  It gives exact cyclic-code
Parseval, Jacobi-mode, cyclotomic-intersection, and cyclotomic-unit/Kummer forms for a projected
collision.  Generic modewise Weil ceilings miss the inversion floor by 127--129 bits, and the
Do Duc--Leung--Schmidt cyclotomic-number hypothesis fails in the production direction
(`P^2<14^k`).  Kummer reciprocity therefore reformulates, but does not certify, simultaneous
Frobenius separation of the roughly `2^29` units.
`_ANT46ProjectedKappaBucketCertificate.lean` turns that separation problem into a checkable exact
finite certificate **format**.  Per-bucket `Nodup` plus disjoint value ranges implies global injectivity, and
a keyed-bucket form makes cross-bucket separation automatic; natural square-and-multiply tables
are proved equal to both production projected maps and feed the inversion-transversal consumer.
This is operational but not compressed: every exact cover has at least `536870912` evaluated
rows, raw 20-byte representatives take 10 GiB, and `2^20` buckets merely give 512 rows per bucket.
The 59/67-bit target groups and 100/93-bit exponents are exact.  A scalar product fingerprint is
formally refuted as a `Nodup` certificate, so the remaining task is to produce and independently
check the full table or discover additional arithmetic compression.
`_BGKMarkedSunflowerInverse.lean` supplies the exact Catalan--Lagrange inverse expressing `D_7`
as an alternating combination of `W_2,...,W_7`.  It also proves that this inverse is equivalent
to the original seventh triangular row once the lower rows are fixed.  At production its absolute
coefficient mass lies between `2^143` and `2^144`; this is coefficient amplification, not an
automatic 143-bit loss because depth-normalized estimates may compensate.  Inversion becomes
useful only with the missing correlated or correctly scaled lower-depth cancellation.
`_BGKSunflowerCorrelationNoGo.lean` closes the generic correlated-inequality variant.  Total
positivity gives exact adjacent **lower** growth inequalities, but the extreme ray supported only
at `D_7=T` has `W_2=...=W_6=0`, arbitrary `W_7`, and the real-rooted/PF-infinity generating
polynomial `T*z^7*(1+z)^(n-14)`.  Even eliminating every proper depth leaves
`13!!=135135=126871+8264`; the primitive sector needs a `6.115...%` arithmetic saving.  The file
also supplies a coefficientwise and additive-character-valued sunflower transform, with a
modulo-29 coefficient vector that reflects every depth-seven characteristic-zero label.
`_BGKPrimitiveDepthSevenSparseCodeNoGo.lean` makes that arithmetic target literal at both
production primes, and `_BGKPrimitiveFoldedAlphabet.lean` sharpens every actual primitive witness
to coefficient alphabet `{-2,-1,0,1,2}`, support and `l1` mass at most `14`, and a nonzero
degree-`<2^29` polynomial.  It also classifies the exact nine local source profiles and attaches a
nonzero resultant `N` with `P | N` and `P <= |N| <= 14^(2^29)` at each production root; the norm
base remains `14` because the endpoint `l1` bound did not improve.  The alphabet is sharp: for
`g=3` in `ZMod 17`, globally disjoint seven-subsets collide with folded vector
`[1,2,1,2,2,2,2,0]`.  Thus alphabet-only kernel-freeness is false even at power-of-two order.
The exact local-profile refinement assigns weights `w_(+-2)=xy`, `w_(+-1)=x+y`, and
`w_0=1+x^2+y^2`.  Its occupancy identity `2A+B+2Z=14` makes the number `B` of unit letters even;
the unique 14-coordinate sector consists entirely of `+-1` letters, and its formal fixed-label
ordered factor is `(7!)^2*C(14,7)=14!`.  All nonunit sectors use at most 13 folded coordinates.
This isolates the leading arithmetic target but supplies no collision saving without
equidistribution; the full cardinality-to-generating-function bijection is not formalized here.
Forgetting the small alphabet still gives a one-check field code of exact distance two, and
Kelley's optimistic 14-nomial root cap remains over 116 bits above the subgroup.  The live code
problem is production arithmetic or an average restricted-alphabet count, not ordinary BCH,
Hamming, Singleton, uncertainty theory, or a universal five-letter obstruction.
`_BGKHashimotoWickSeparationNoGo.lean` closes the ordinary graph-normal-ordering variant.  The
degree-fourteen Ihara--Bass polynomial removes only the 14 cyclically adjacent reversals, whereas
Wick subtraction sees all `C(14,2)=91` first-pair placements; the residual coefficient is exactly
`77d+14`.  An explicit closed cyclically nonbacktracking word with repeated directions survives,
and two unit-phase families with the same adjacency eigenvalue have opposite ordered-injective
transforms.  A univariate Hashimoto/Chebyshev polynomial therefore cannot recover the packet;
one must retain the dilation-coloured operators at `b,2b,...,7b` and still solve the primitive
arithmetic problem.  A genuinely new Ramanujan cap would close the public raw-moment route
(coefficient `4096`), though it is not by itself a direct extraction of `D_7`; Ihara theory on this
regular graph only relabels the original Paley spectrum.
`_BGKDilationColoredNewtonOperatorNoGo.lean` constructs that missing graph object exactly.  The
seven convolution operators commute and share the additive-character basis; substituting them in
the full Newton polynomial gives eigenvalue `7!*e_7`, the ordered-injective transform.  This is a
real coordinate advance, but not a norm bound: all seven colours have identical complete marginal
Schatten profiles, while a two-frequency coefficient-scale model with the same marginals has
Newton energies `66816<126871<25401600`.  The Newton scalar is also sign-indefinite on commuting
contractions.  The surviving operator theorem must therefore control the mixed arithmetic joint
law `(eta_b,...,eta_(7b))`; commutativity, marginal norms, and generic Schur/SOS positivity cannot
provide the `8264` saving.
`_BGKDilationPermutationCopulaNoGo.lean` strengthens the blindness result to one genuine common
dilation action.  On `ZMod 13`, two equimeasurable sign profiles generate colours by
`P_f(j,b)=f(jb)` and hence have identical marginal moments for every colour and exponent, but
their normalized Newton energies satisfy `953600<13*126871<64641152`.  These profiles are not
claimed to be subgroup periods; the theorem isolates the extra missing datum precisely as
Fourier-of-a-multiplicative-subgroup arithmetic, beyond dilation compatibility itself.
`_BGKActualJointPeriodLaw.lean` now pins the first layer of that missing datum.  Every mixed
coloured moment is exactly `q` times a weighted subgroup collision count.  Exact modular checks
put `1,...,7` in distinct cyclotomic classes at both production primes, so their nonzero-frequency
Gram matrix is a regular simplex: diagonal `q*n-n^2`, off diagonal `-n^2`.  This refutes aligned
copulas for the actual periods, but its pair correlation is 123--124 bits below the leakage needed
for `8264`.  The exact first deleted-pair energy is `q*(A+n-2M)`, where `A` is additive energy and
`M` counts midpoint resonances.  Under a nonzero-shift representation cap `2^22`, the first-prime
antipodal floor makes a selected `3 -> 2` Wick defect demand `M>2^59` while the cap gives
`M<=2^52`.  Higher signed weighted-collision correlations remain open.
`_BGKSevenStepFlatteningProductionNoGo.lean` gives the entropy route an exact positive socket.
The normalized injective chi-square allowance lies between `2^-36` and `2^-35`.  Across the six
transitions after the first step, uniform contraction numerators must have product at most
`126871`: `7^6=117649` fits, while `8^6=262144` does not, so each step needs more than 27 L2
bits.  Ordinary positive BSG loses 98--99 bits before extracting one point; even granting the
classical shifted-intersection cap `4*n^(2/3)=2^22` supplies only eight bits, exactly 19 short per
step; Hart's sixfold-covering density gate is reversed by over 1048 cleared bits.  The viable
entropy theorem must be centered and trajectory-weighted, not a raw-energy inverse theorem or a
support-growth statement.
`_BGKWickTrajectoryDefectBudget.lean` sharpens this to a one-unit target.  The natural six Wick
numerators are `3,5,7,9,11,13`, with product `135135`, while the exact production trajectory
allowance lies strictly between `126871` and `126872`.  Lowering any one numerator by one makes
the product at most `124740<126871`; enough margin remains to multiply all six profile bounds by
`501/500` (a `0.2%` per-step overrun).  Abstract six-ratio telescoping theorems then prove the
end-to-end depth-seven target from either the exact or robust profile.  This is a sharp new socket,
not a closure.  An exact distributed alternative lowers only the two final numerators by one half,
`11 -> 10.5` and `13 -> 12.5`; its product is `124031.25`, and the same sixfold robust overhead
still gives only `125527.08...<126871`.  This is not a closure: the missing theorem must produce
either certified profile while keeping all finite-population losses inside the robust margin.
`_BGKCenteredTrajectoryContraction.lean` installs this on the actual forward subset trajectory.
Its six local bounds telescope to the coefficient-`126871` variance target, and its deleted-
diagonal Newton identity retains all colours `eta_b,...,eta_(7b)`.  A genuine order-eight subgroup
in `F_17` forces every universal six-step product to be at least `8^6`, ruling out a field-uniform
contraction theorem.  At production, the forced antipodal zero-sum fiber gives the unconditional
first-ratio lower bound `n*Z_2/Z_1 > 3+2^-29`.  Thus neither Wick `3` nor the robust selected cap
`2*(501/500)` is valid at the first transition: the one-unit defect must occur at one of the five
later transitions.  The antipodal lower envelope lies below the ordinary robust cap `3.006`, but
this is not an upper bound on the complete first ratio.
`_BGKLaterTransitionDefectLedgers.lean` clears every remaining rational transition denominator.
For collision defects `Delta_r=q*C_r-C(n,r)^2`, a cap `A/B` is exactly
`B*n*(r+1)^2*Delta_(r+1) <= A*(n-r)^2*Delta_r`.  It records all five robust ledgers and the
distributed final obligations with coefficients `10521` and `12525`.  Production crosses the
ambient birthday scale violently between depths five and six:
`2^14*C(n,5)<q<2^15*C(n,5)` but `2^12*q<C(n,6)<2^13*q`.  The final transition is relatively
cheapest (`12/13`), while `5 -> 6` is the first structurally load-sensitive step.
`_BGKCubicSignedWeightedCollision.lean` resolves the first surviving `2 -> 3` transition into an
exact signed census.  For `J_3=eta_1^3-3*eta_1*eta_2+2*eta_3`, its full energy divided by `q` is
`C_111,111+9*C_12,12+4*n-6*C_111,12+4*C_111,3-12*C_12,3`; deleting frequency zero subtracts
`(n*(n-1)*(n-2))^2`.  The robust defect is equivalent to a lower bound on the favorable mass
`6*C_111,12+12*C_12,3`.  G186's unsigned Young estimate controls the positive `C_12,12` term but
drops exactly those favorable correlations, so it cannot certify the defect alone.
`_BGKProductionBirthdayCrossover.lean` and its exact probe rank `6 -> 7` first empirically and
`5 -> 6` second.  Favorable order-64 cells satisfy the distributed late profile, but the direct
crossover cell `(n,p)=(64,8001281)` has both late ratios above ordinary Wick.  Birthday density
alone is therefore refuted; the remaining theorem must use the actual joint-period arithmetic.
`_BGKLateNewtonSignedCovariance.lean` now gives that arithmetic an exact signed coordinate system.
The `j`th Newton join has physical phase `j*x + sum S`, its Fourier transform is
`p_j*e_(d-j)`, and cross Parseval turns every entry of the depth-six or depth-seven covariance
matrix into one structured collision count.  The alternating packets are proved equal to the
existing ordered-injective transforms `J_6,J_7`; after exact DC subtraction their raw signed
forms are `36*C_6` and `49*C_7`, so the nonzero ledgers are literally `(6!)^2*Delta_6` and
`(7!)^2*Delta_7`.  The alternating Newton signs leave nine
favorable-sign unordered pairs at depth six and twelve at depth seven; this describes their
algebraic coefficients, not the sign of each centered covariance.  Unsigned Young/triangle
estimates erase them.  `_BGKLateNewtonDominantPairSocket.lean` isolates the empirically dominant two-colour
energy `L=E_11+E_22-2*E_12` and a signed tail `R`.  Exact scalar consumers allocate
`10500+21=10521` at `5 -> 6` and `12500+25=12525` at `6 -> 7`.  The accompanying exact probe is
two-sided: favorable cells pass the combined `U_1-U_2` cap with a nonpositive tail, while adverse
cells can still have ample negative `E_12`; covariance alone therefore does not distinguish
success.  The new theorem-shaped target is a production bound on the centered energy of
`U_1-U_2`, plus the displayed small signed-tail budgets.  The probe is not a production theorem.
`_BGKLateNewtonTwoColourPhysicalBridge.lean` removes the abstract-leading-term seam.  It proves
`C_11+C_22-2*C_12` is the physical square mass of `U_1-U_2`, subtracts the exact DC imbalance,
defines literal complementary tails, and feeds the `10500/21` and `12500/25` sockets with actual
field collision counts.  Erase/insert equivalences cancel the common repeated-`U_1`/fresh-`U_2`
sector fibrewise.  Fresh weight one is exactly `(r+1)` copies of the ordinary next-subset
histogram, so the surviving profile is `(r+1)*a_(r+1)` minus the fresh weight-three residual.
Thus the live bound is a signed boundary-profile estimate, not a heuristic covariance split.
`_BGKC12TranslateIntersectionReduction.lean` separates the actual favorable cross count as
`C_12=sum_t W_G(t)*R_r(t)`, where `W_G(t)=#{y in G:2*y-t in G}` is a literal shifted cyclotomic
intersection row and `R_r` is the adjacent subset-difference row.  A sharp two-cell no-go proves
that masses, square masses, nonnegativity, Cauchy, and separate Gram diagonals cannot force this
inner product.  Their exact masses are `n^2` and `C(n,r)C(n,r-1)`; subtracting the mean product
defines one centered alignment `A_r`, and both production gates are formal lower bounds on
`A_5,A_6`.  The forced mean terms have 319 and 374 bits respectively.  The missing theorem is
joint arithmetic alignment of the two actual rows.
`_BGKC12CyclotomicHalfCapNoGo.lean` makes the literature connection exact: for `t != 0` in odd
characteristic, `W_G(t)` is the plus-one intersection of the two dilates `(-2/t)G` and
`(-1/t)G`.  The [Betsumiya--Hirasaka--Komatsu--Munemasa half-cap
theorem](https://arxiv.org/abs/1109.6539) therefore applies at both production primes, whose
characteristics satisfy `p > 3*n/2-1`.  Its conclusion still has the wrong information direction:
an exact four-class witness obeys the half cap, mass, and complete marginal square-mass data while
its cross alignment ranges from zero to the aligned value.  The exact 38-cell
`probe_bgk_c12_alignment.py` audit is stronger evidence against a sign shortcut: `A_r<0` in
19 cells, all four alignment-sign/gate quadrants occur, strict `W/R` comonotonicity fails in
36 cells, and every cell has a negative pointwise centered product.  The production target is the
relative gate `A_r >= A_required(C_11,C_22,Delta_r)`, not `A_r >= 0`; the probe makes no production
extrapolation.
`_BGKC12AdditiveSpectralBridge.lean` supplies the exact dual coordinate:
`R_r(t)=sum_s a_r(t+s)a_(r-1)(s)`, `W_hat(b)=eta(2b)*conj(eta(b))`, and
`R_hat(b)=e_r(b)*conj(e_(r-1)(b))`.  Consequently `A_r` is exactly the nonzero-frequency signed
inner product `sum eta(2b)conj(eta(b))conj(e_r(b))e_(r-1)(b)`.  A two-frequency theorem shows that
identical pointwise and total spectral magnitudes still permit opposite inner-product signs, so
separate eigenvalue/norm estimates cannot close the gate.  `_BGKC12DilationOrbitCompression.lean`
compresses both rows to multiplicative-orbit representatives, proves the zero-orbit dichotomy,
and factors both `C_12` and `A_r` by `|G|`.  This yields exact divisibility and a quotient-level
gate, but no sign: the missing datum is relative phase/placement on those representatives.
`_BGKLateNewtonJohnsonBoundaryNoGo.lean` audits the tempting slice-spectral shortcut.  On each
pointed subset fibre, forgetting the mark is rank one: the constant direction has eigenvalue equal
to the fibre size and every zero-sum direction lies in its kernel.  The exact variance identity and
the witness `(1,-1)` rule out every finite full-energy bound from the unpointed projection,
including the `10.5/12.5` constants.  The physical bridge explains the obstruction: fresh weight
one is mark-independent, but fresh weight three retains the nontrivial `sum(T)+2*x` twist.  A
surviving Johnson theory must be pointed and colour-sensitive, then still use subgroup arithmetic.
`_BGKFirstCollisionCovarianceLedgerBridge.lean` audits the adjacent G189--G193 repetition route.
It proves the exact `29/30` and `41/42` internal cancellation thresholds, but also the correct
deletion identity
`V(J+P)=V(J)+sum_i V(P_i)+Cov_off(P)+2*Cov(J,P)`.  Thus internal repetition covariance is not the
injective ledger carrier.  A formal counterprofile has perfect internal cancellation and still
fails the late ledger; G191 proves positive covariance for a genuine lexicographic subgroup
partition, while G193 proves the same sign for G192's symmetric depth-three replacement.
Even returning the full repeated-sector reservation changes `126871` only to
`127009`, still `8126` below Wick's `135135`.  The principal saving must occur in the injective
Newton trajectory, not in a generic repetition-sector sign claim.
`_BGKCyclotomicKreinSchurNoGo.lean` closes the positivity-only association-scheme variant.
Pointwise multiplication of translation kernels is additive convolution of their Fourier
profiles, and every nonnegative multiplicative-orbit profile remains nonnegative and
orbit-invariant under every convolution power.  Consequently the complete Schur/Krein hierarchy
leaves the centered unit-mass LP exactly equivalent to the worst Gaussian-period square.  With
only the valency bound the production relaxation misses by 191--192 bits and supplies none of the
exact `8264/135135` primitive saving.  Any surviving association-scheme proof must use the
arithmetic values, integrality, or nonlinear coupling of intersection numbers, not their
positivity alone.
`_BGKCyclotomicIntersectionIntegralityAudit.lean` then retains the literal integer structure
constants.  Their character transform is exactly the product of relation periods, total mass and
multiplier-orbit invariance are formal, and Cauchy--Davenport excludes support on one cyclotomic
class at both production primes.  But the standard integral relaxation still admits the row
`(2^30-1,1)`.  It forces one leaked unit, whereas the `8264` coefficient gap requires exactly
`ceil(8264*2^30/135135)=65663244`, between `2^25` and `2^26`.  A surviving scheme theorem must
control the correlated placement and values of many intersection numbers, not row integrality,
mass, or support alone.

**Dyadic two-scale recursion (2026-07-11).** `_DQR23TwoScaleCenteredRecursion.lean` proves the
exact sibling law `eta_(G union aG)(b)=eta_G(b)+eta_G(ba)`, the full signed binomial ledger at
moment 14, and the quadratic anticorrelation `sum_(b != 0) eta_G(b)eta_G(ba)=-|G|^2`.
`_DQRSecondMomentAnticorrelationNoGo.lean` shows why the last identity is not yet a contraction:
a rational mean-zero sibling array can have negative cross-correlation while its coarse
fourteenth moment grows far beyond the Gaussian factor `2^7`. The live DQR residual is therefore
a higher mixed-moment sign law, not a second-moment estimate.
`_DQR4CrossMomentRepLocalization.lean` makes that law pointwise: every `(k,1)` cross moment is
exactly `q*|G|*(f_k(a)-|G|^k/q)`, the centered `k`-fold representation count at the adjoining
twist `a`.
The subsequent general-stratum and twist-average files identify every mixed term with a centered
dilated rep--rep correlation and factor its average over all twists.  Thus DQR-4 is now a precise
29-point discrepancy problem at the distinguished quotient involutions.  The adjoining symmetry
reduces the ledger to seven paired cross strata, but small cells refute uniform contraction:
at `p=65537`, the moment-step ratio normalized by `2^7` is `23.70` for `n=16` and `28.41` for
`n=32`, with every cross contribution aligned.  Mean-zero/inversion symmetry can concentrate
arbitrarily close to all L2 mass at the involution, while exact level telescoping returns the
endpoint Paley moment.  A surviving DQR route therefore needs new field-specific exceptional-level
control; averaging, Cauchy--Schwarz, and recursion alone are closed.

**Projective accident packets (2026-07-11).**  `_ANT46RungTwoAccidentOrbit.lean` now closes the
full projective `S₄` classifier.  For an odd-characteristic accident the identity fibre has size
`1`, `2`, or `6`; the two-pair pattern is lawful, and the certified production `-3` exclusion
removes the `3+1` pattern.  Hence every production accident orbit has size `24` or `12`, and the
total accident count is divisible by `12`.  This does not prove accident-freeness: the exact next
socket is any independent bound `<12` (or a direct emptiness/resultant certificate).  The same
file now gives that certificate an exact cyclotomic-unit form: for
`kappa_n(x)=(x-1)^n`, accident-freeness is equivalent to injectivity modulo inversion, and
`#accidents=sum_v(k_v^2-2k_v+s_v)=sum_v k_v^2-2n+3` over the signature fibres.  At production it
suffices to exclude `P_i | Disc(K_n) K_n(2^n)` for a canonical degree-`2^29-1` polynomial; the
remaining algorithmic problem is a dyadic discriminant/resultant recurrence, not triple
enumeration.
`_ANT46KappaDyadicRecurrence.lean` proves that recurrence:
`K_(2n)=Sq(K_n)*J_(2n)`, with `J_(2n)` an explicit resultant of the primitive trace polynomial.
The recurrence and bad-prime criterion agree through `K_32`, while square-only and recycled-`K`
scalar recurrences fail.  At production the trace circuit has only 28 levels but width `2^28`, so
the sharp successor is a new norm-collapse invariant; this is not an impossibility result for all
logarithmic certificates.

The `_BGK*` files landed 2026-07-10 hang the ENTIRE depth ladder off the single named open
Prop `WorstCaseIncompleteSumBound` (the BGK sup-bound), end to end at literal prize numbers:
`_BGKSupBoundMomentTower` (every-depth moment tower) → `_BGKDepthREnergyLaw` (exact
`∑‖η_b‖^{2r} = q·E_r`; §8 independence form mod BGK) → `_BGKProductionDepthFiveWeld` /
`_BGKInjectiveFiveWeld` / `_BGKFiberSquareCensusBridge` (BGK ⟹ the G112 production socket's
exact conclusion, replacing its open variance certificate) → `_BGKNineBitGap` (**the sharpest
open sub-target**: trivial anchor `M = 2⁶⁰` proven; weld fires at `M ≤ 2⁵¹`; the whole
depth-five lane = a 2⁹ sup-bound saving over trivial, i.e. `‖η_b‖ ≤ |G|^0.85`). See
`docs/kb/deltastar-466-bgk-moment-tower-and-production-welds-2026-07-10.md`.

## Status of the original #334 lane files

| file | target | status (2026-07-01) |
|------|--------|---------------------|
| `ThornerZamanS128.lean` + `ThornerZamanInstance.lean` | discharge `TZPrimeSupply` (window `[n^β, 2n^β]` has ≥ supply primes `≡ 1 mod n`) | **Concrete ladder LANDED** (axiom-clean, explicit-prime certificates): β=2 through `n = 32768` (`tzPrimeSupply_{8,16,…,32768}_two`), β=3 through `n = 64`, β=4 through `n = 64`, β=5 at `n = 8` — all in `ThornerZamanInstance.lean` (+ `CanonicalWidthFourConcreteTZ.lean`). The *general/asymptotic* Thorner–Zaman PNT-in-APs form remains a named open hypothesis (dossier v3 §6 Tier 3, "largely dischargeable"). |
| `CurveDecodability.lean` | [GG25] Def 3.1 curve decodability → [Jo26] half | OPEN, multi-brick (dossier v3 §6 Tier 3; folded-RS capacity pin via `curveDecodable_of_structured_close_set_budget` is the live adjacent lane). **RE-PLAN TARGET (2026-07-10):** GGSW arXiv:2607.08516 (Jul 9) casts curve-decodability directly as a row-span-constrained LCL property with black-box transference from subspace designs — formalize against THAT formulation, not the [Jo26] proxy; see `docs/kb/deltastar-466-litsweep-2026-07-10.md`. ([JLR 2601.10047] is withdrawn, subsumed by GG25 — update stale citations.) |
| `EquivariancePin.lean` | Lean equivariance pin for the n=12 orbit reduction | LANDED → `../MCAEquivariance.lean` (engine) + `../MCAEigenstackOrbitLaw.lean` (orbit law, counting) |

Historical note: predecessors #334/#357/#444/#464 are closed, and #466 is the final predecessor
campaign now migrated to standalone issue #1. The `_`-prefixed files in this directory are the
accumulated lane record. Check `../DISPROOF_LOG.md` (`466-r*` historical round tags, still
accumulating) before re-attempting anything.
