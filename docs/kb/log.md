# Knowledge Base Log

This file is append-only.
Each entry records a notable KB event: initialization, ingest, audit creation, or major update.

## [2026-04-15] initialize | docs/kb

Created the initial knowledge-base subtree:

- `docs/kb/README.md`
- `docs/kb/index.md`
- `docs/kb/log.md`
- `docs/kb/papers/`
- `docs/kb/concepts/`
- `docs/kb/audits/`
- `docs/kb/queries/`
- `docs/kb/sources/`
- `docs/kb/_generated/`

## [2026-04-15] seed | initial paper pages

Seeded the first repository-local paper pages for currently active or already cited references:

- `ACFY24`
- `ACFY24stir`
- `BCIKS20`
- `BCS16`
- `BBS24`
- `DP24`

## [2026-04-15] seed | citation coverage stubs

Scaffolded paper pages and source metadata for the remaining citation keys currently used in
`ArkLib/**/*.lean`:

- `AHIV22`
- `BSS08`
- `FRI1216`
- `GWZC19`
- `JM24`
- `LFKN92`
- `LPS24`
- `PS94`
- `Poseidon2`
- `STIR2005`
- `Spi95`
- `codingtheory`
- `listdecoding`

## [2026-04-15] generate | bibliography and citation registries

Added initial generated outputs:

- `docs/kb/_generated/references.json`
- `docs/kb/_generated/lean-citations.json`

using the new scripts under `scripts/kb/`.

## [2026-04-15] migrate | list-decoding audit

Promoted the existing paper audit into:

- `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`

and updated tracked wiki navigation to point to the KB copy rather than to a branch-local
untracked file.

## [2026-04-15] refine | high-value paper pages

Replaced initial stubs with ArkLib-specific summaries for:

- `AHIV22`
- `LFKN92`
- `GWZC19`
- `FRI1216`

These are now better landing pages for active review and protocol work in the `InterleavedCode`,
`Sumcheck`, `Plonk`, and `Fri` subtrees.

## [2026-04-15] automate | review context helper

Added:

- `scripts/kb/review_context.py`

to resolve citation keys, KB paper pages, source metadata, and public URLs from explicit keys or
changed Lean files, with output shaped for `.github/workflows/review.yml`.

## [2026-04-15] refine | second paper-page batch

Replaced initial stubs with ArkLib-specific summaries for:

- `JM24`
- `LPS24`
- `Poseidon2`
- `BSS08`
- `STIR2005`
- `listdecoding`
- `codingtheory`

This improves the KB coverage for the `AGM`, `Data/Hash`, `ProofSystem/Stir`, and
`JohnsonBound` areas.

## [2026-04-15] refine | final cited-paper stubs

Replaced the remaining cited-paper stubs with ArkLib-specific summaries for:

- `PS94`
- `Spi95`

and added a concept hub:

- `docs/kb/concepts/polishchuk-spielman-lineage.md`

for the corrected-vs-original Polishchuk-Spielman source lineage.

## [2026-05-03] audit | BCIKS20 Appendix A rational functions

Added:

- `docs/kb/audits/bciks20-appendix-a-rational-functions.md`

to track the rational-function and Hensel-lifting declarations supporting the BCIKS20
list-decoding branch.

## [2026-06-04] concept | oracle-reductions architecture page

Added the concept page requested in issue #480:

- `docs/kb/concepts/oracle-reductions.md`

It documents the IOR layer conceptually (prover/verifier interaction model, oracle verifiers and the
`embed` mechanism, the Basic/Execution/Security separation of concerns, reduction-style security, and
sequential composition + BCS transform), grounded in the real `ArkLib/OracleReduction/**` modules. It
cross-links with `concepts/interactive-oracle-proofs.md` and is registered in `index.md` and
`concepts/README.md`. Per the maintainer, no docstrings were added to `Basic.lean` (rewrite in #433).

## [2026-05-03] prove | BCIKS20 function-field regularity API

Updated `ArkLib/Data/Polynomial/RationalFunctions.lean` with an explicit function-field `T`
variable, regular-element closure lemmas, and a concrete low-degree `ξ` regularity helper.
The Appendix A rational-functions audit now records this as the next denominator-clearing layer
toward `ClaimA2.ξ_regular`.

## [2026-06-13] synthesize | power-word zero-sum list law for delta*

Added:

- `docs/kb/deltastar-powerword-zero-sum-law-2026-06-13.md`

to record the exact all-`k` power-word sub-Johnson list identity from
`PowerWordListBound.lean`, its ten connections to the #389/#371 supply programme, and the
next symmetric-function fiber targets.

## [2026-06-26] refine | delta-star slack-profile cap equivalence

Updated:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackDominance.lean`
- `docs/kb/deltastar-464-profile-slack-dominance-2026-06-26.md`
- `docs/kb/deltastar-464-profile-slack-cap-collapse-2026-06-26.md`

to record that a slack-profile representative scheme is exactly the existing profile-cap interface
with the induced cap `bad(rep p) + slack p`.  The update adds axiom-clean equivalence lemmas and
preserves the critical conclusion: only a genuine compressed-profile stability theorem would make
the route mathematically stronger than direct profile caps.

## [2026-06-26] prove | profile-fiber oscillation certificate

Extended:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackDominance.lean`
- `docs/kb/deltastar-464-profile-slack-dominance-2026-06-26.md`

with `ProfileRepresentativeInFiber`, `ProfileFiberOscillationBounded`, and
`ProfileFiberOscillationCertificate`.  The new certificate proves the existing slack certificate,
feeds the same open-core and delta-star consumers, and has an exact three-way failure surface:
representative misses its used fiber, same-profile oscillation exceeds slack, or the
representative-plus-slack budget is above `B`.  Endpoint lemmas make explicit that the coarsest
profile collapses oscillation back to a global pairwise bad-count diameter bound, while the identity
profile, and more generally any injective profile with zero slack and in-fiber representatives, are
exactly the original all-stack incidence theorem.

## [2026-06-26] prove | slack-profile floor contract

Added:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackFloorBridge.lean`
- `docs/kb/deltastar-464-profile-slack-floor-contract-2026-06-26.md`

The new bridge states the exact floor-facing contract for slack profiles.  A floor-localization
proof may now feed `ProfileFiberSlackBudgeted` directly through
`FloorGoodProfileSlackBudget`; together with independent slack domination this gives
`WorstCaseIncidenceBounded` and the usual delta-star pin.  The failure surface is exact: floor still
bad, some stack exceeds its representative-plus-slack allowance, or some used profile's
representative-plus-slack allowance is above budget.  This keeps the off-BGK floor lane useful as an
obstruction-removal tool without laundering it into a proof of the universal #464 floor.

## [2026-06-26] refine | singleton floor dominator gate

Added:

- `docs/kb/deltastar-464-singleton-dominator-gate-2026-06-26.md`

and extended:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/FloorNecessaryNotSufficient.lean`

with `OneDirectionMaximizes`, the exact positive singleton bridge
`allDirectionsBounded_of_oneDirectionBounded_and_maximizes`, and the falsifier
`not_oneDirectionMaximizes_iff_exists_larger`.  This isolates the missing theorem behind the
off-BGK floor route: a bounded binder/floor direction can control the MCA supremum only if it is a
true global bad-count maximizer.

## [2026-06-26] refine | profile granularity endpoints

Added:

- `docs/kb/deltastar-464-profile-granularity-endpoints-2026-06-26.md`

to tie the stack-profile cardinality tradeoff to the slack-profile proof obligations.  The note
records the two dead endpoints: constant profiles require global pairwise oscillation control, while
injective profiles are just relabelings of the all-stack theorem.  The remaining live target is a
genuinely non-injective profile with a real same-fiber oscillation theorem.

## [2026-06-26] refine | zero-slack profile factorization

Added:

- `docs/kb/deltastar-464-zero-slack-profile-factorization-2026-06-26.md`

and extended:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackDominance.lean`

with `ProfileBadCountRepresented` and exact consumers/falsifiers.  With in-fiber representatives,
zero same-profile oscillation is equivalent to exact bad-count factorization through the chosen
profile representative.  The zero-slack certificate now fails exactly by a stack whose count differs
from its representative, or by an above-budget used representative.

Follow-up: the same file now exposes the representative-free invariant
`ProfileBadCountFiberConstant`.  Zero same-profile oscillation is equivalent to fiberwise bad-count
constancy, and representative factorization is just the in-fiber-section form of that invariant.
The representative-free consumer feeds this invariant plus an in-fiber section and used-representative
budget directly to the incidence bound and delta-star pin.  Failure is exactly a same-profile pair
with unequal bad counts.

## [2026-06-26] refine | floor closure max normal form

Updated:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorClosureContract.lean`
- `docs/kb/deltastar-464-floor-closure-contract-2026-06-25.md`

to state `FloorClosureAtField` directly in max-containment form.  The concrete floor certificate is
now equivalent to floor-goodness, a bounded candidate family, and `FamilyContainsGlobalMax`; its
failure is exactly a bad prime, a budget-missing representative, or lack of global-max containment.

Follow-up: `_FloorClosureContract.lean` now exposes the sharper
`FamilyContainsBudgetedGlobalMax` and `FloorClosureBudgetedMaxAtField` normal forms.  One listed
representative that is both within budget and globally worst is sufficient for the universal
incidence bound; budgeting every nonmaximal family member is stronger than necessary.  Failure is
exactly a bad floor prime, or every listed representative being either above budget or beatable by
another stack.

Follow-up: the Linnik and Thorner-Zaman candidate-list wrappers now consume
`FamilyContainsBudgetedGlobalMax` directly.  Exact singleton floor-bad lists plus least-prime supply
only discharge field floor-goodness; the remaining incidence proof is the single budgeted global
maximizer certificate.

## [2026-06-26] refine | norm-factorization smooth scanner

Added:

- `docs/kb/deltastar-464-norm-factorization-smooth-support-scanner-2026-06-26.md`

and updated `_NextNormFactorizationClustering.lean` with exact scanner forms for smooth norm
persistence and above-threshold shared prime factors.  Smooth persistence now implies empty
above-`B` supports, pairwise disjoint thresholded supports, and zero thresholded cluster rate; failure
returns either a large prime factor or a shared large prime.  The off-diagonal domination bridge is
also sharper: it no longer needs a separate `0 <= c` hypothesis.

## [2026-06-26] refine | line-list ratio-census budget gate

Added:

- `docs/kb/deltastar-464-line-list-ratio-census-budget-2026-06-26.md`

and updated `LineListReduction.lean` with named local sets for the affine-line bad scalars and
appearing codewords.  A budgeted line list now directly gives
`lineBadScalars.card <= L * floor(n/a)`, while any over-budget bad-scalar count refutes the proposed
line-list budget by forcing more than `L` appearing codewords.  The residual is therefore a genuine
line-list-size theorem, not another per-codeword ratio-census identity.

Follow-up: `CodewordHeavyScalar.lean` and `LineListReduction.lean` now include the support-aware
variant.  If the direction has `z` zero coordinates and `z < a`, each codeword contributes at most
`directionSupportSet.card / (a - z)` heavy scalars, with matching line-list consumers and
contrapositives.  This removes the nowhere-zero direction assumption without changing the residual:
the open work is still bounding the number of appearing codewords.  The complementary
`a <= z` branch is now an explicit near-code/zero-direction residual instead of a hidden
nowhere-zero hypothesis.

Follow-up: `LineListReduction.lean` now exposes the family-level production target
`UniformSupportLineListBudgeted` and the consumer `SupportAdjustedLineBadScalarsBudgeted`.  A
uniform eligible-line list bound gives the support-adjusted bad-scalar budget on every eligible
affine line.  The exact falsifiers are an eligible line with more than `L` appearing codewords, or
an eligible line whose bad-scalar count beats the support-adjusted budget.

Follow-up: the zero-direction complement is now sharp.  `directionZeroAgreementSet` records
zero-coordinate agreements between a codeword and the line offset; if that count already reaches
`a`, then the fixed-codeword heavy-scalar set is all of `F`, and a codeword in `rsCode dom k` forces
`lineBadScalars = univ`.  Thus any nontrivial line bad-scalar bound must rule out such
zero-direction near-code witnesses.

Follow-up: the same zero-direction branch is now packaged as a necessary condition for production
budgets.  `UniformLineBadScalarsBudgeted dom k a B` with `B < |F|` forces
`UniformZeroDirectionSafe dom k a`; conversely, any unsafe zero-direction line refutes every uniform
budget below field size.  This matches the prize polarity, where the desired budget is near `n` and
the field is much larger.

Follow-up: the line-list route now has a complete support/large-zero decomposition.  A uniform
bad-scalar budget follows from a support-eligible line-list theorem, an arithmetic
`SupportAdjustedBudgetFits` check, uniform zero-direction safety, and a separate
`LargeZeroSafeLineBadScalarsBudgeted` theorem.  The large-zero safe residual is now the exact
remaining branch rather than an informal exception to the support-fiber argument.

Follow-up: `not_uniformLineBadScalarsBudgeted_iff_eligible_or_unsafe_or_largeZero_safe` now gives
the exact subfield-budget failure trichotomy: eligible overbudget, zero-direction saturation, or
large-zero safe overbudget.  Added `docs/kb/deltastar-464-large-zero-trichotomy-2026-06-26.md`,
which criticizes the previous line-list optimism and identifies the next possible tool as a
punctured zero-stratified line-list theorem.

Follow-up: the punctured zero-stratified tool is now formalized.  `CodewordHeavyScalar.lean` proves
the per-codeword denominator `support(u1)/(a - #zeroAgreement(c,u0,u1))`, and
`LineListReduction.lean` lifts it to `puncturedZeroStratifiedLineWeight` plus consumers for
`LargeZeroSafeLineBadScalarsBudgeted` and `UniformLineBadScalarsBudgeted`, plus a bridge from
large-zero safe bad-scalar failure to punctured-weight failure.  The exact regrouping
`puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata` rewrites the same weight as a
sum over `t < a` zero-agreement strata.  Added
`docs/kb/deltastar-464-punctured-zero-stratified-tool-2026-06-26.md`; the remaining theorem is now
a uniform bound on that punctured weight, or a scanner counterexample to it.

Follow-up: `LineListReduction.lean` now exposes the `N(t)` envelope theorem directly.
`ZeroAgreementStrataCardBudgeted` plus `ZeroAgreementStrataBudgetFits` bound the punctured weight,
and the uniform large-zero versions imply `UniformPuncturedZeroStratifiedLineBudgeted`.  The next
non-analytic theorem is an actual cardinality envelope for the exact zero-agreement strata.

Follow-up: the `N(t)` envelope now has exact scanner-facing failures.  A failed stratum-cardinality
budget returns a large-zero safe line and a concrete overfull zero-agreement stratum; a failed
arithmetic fit returns a large-zero direction whose weighted `N(t)` sum already exceeds `B`.  If the
arithmetic fit is fixed, any failed punctured budget must come from an overfull stratum.

Follow-up: the `N(t)` envelope now composes with the full line-list trichotomy.  With large-zero
stratum arithmetic fixed, a uniform bad-scalar budget failure is eligible overbudget, zero-direction
saturation, or an overfull large-zero stratum.  If the support-eligible line-list theorem,
support-fit arithmetic, and zero-direction safety are also fixed, the only remaining witness is the
overfull large-zero stratum itself.

Follow-up: the overfull stratum target now splits into raw fixed zero-subset coordinate fibers.
Added `docs/kb/deltastar-464-coordinate-fiber-residual-2026-06-26.md`.  `coordinateAgreementFiber`
covers each stratum by `t`-subsets of `directionZeroSet(u1)` and proves the endpoint
`#S >= k -> card <= 1`.  With coordinate-fiber arithmetic fixed, a failed uniform bad-scalar budget
now reports an overfull coordinate fiber, not just an overfull stratum.

Follow-up: the high zero-agreement range is now discharged at stratum level.  If `k <= t`, then
`#zeroAgreementStratum(t) <= choose(#directionZeroSet(u1), t)`.  Therefore any overfull stratum
whose envelope already covers this binomial ceiling must live in the low interpolation range
`t < k`; the full production scanner now has the same low-stratum refinement.

Follow-up: the raw coordinate-fiber interpolation count is now formalized:
`#coordinateAgreementFiber(S) <= |F|^(k - #S)` with only the standard Lean axioms.  The
coordinate-fiber scanner also has a low-range form: if `M(t) >= 1` on `k <= t < a`, then a failed
production budget reports either zero-direction saturation or a large-zero safe overfull coordinate
fiber with `t < k`.  The remaining question is the weighted binomial arithmetic or a stronger
support-aware low-fiber theorem.  A field-power production wrapper now shows that, once this
arithmetic fit is fixed, a uniform bad-scalar failure can only be zero-direction saturation.

Follow-up: the field-power arithmetic fit now exposes its first necessary condition.  The
`t = 0` summand alone forces `|F|^k * support(u1) / a <= B` on every large-zero direction, and one
direction violating this zero-term inequality refutes the raw field-power coordinate-fiber fit.
If a large-zero direction also has support at least `a`, the fit already forces `|F|^k <= B`; thus
`B < |F|^k` refutes the naive interpolation envelope whenever such a direction exists.

Follow-up: that witness now exists under the simple parameter inequality `2a <= n`.  The direction
with `a` zero coordinates and value `1` elsewhere is large-zero but still has support at least `a`.
Consequently the raw field-power coordinate-fiber fit is formally impossible whenever
`2a <= n` and `B < |F|^k`; future progress must beat the unconstrained affine fiber count using
support/appearance geometry.

Follow-up: the obstruction is now per-summand, not only `t = 0`.  Any field-power fit must satisfy
each weighted term individually, and if the support covers `a - t`, it already forces
`choose(#zeroSet(u1), t) * |F|^(k-t) <= B`.  This gives a sharper arithmetic scanner for refuting
candidate low-stratum envelopes before returning to geometric codeword structure.

Follow-up: added `docs/kb/deltastar-464-field-power-arithmetic-obstruction-2026-06-26.md` and
`LineListArithmeticObstruction.lean`.  For every `z <= n`, the source constructs a direction with
exactly `z` zero coordinates and support `n-z`.  Therefore `a <= z`, `t < a`, `a - t <= n-z`, and
`B < choose(z,t) * |F|^(k-t)` refute the raw field-power coordinate-fiber fit.  The remaining
positive route must count appearance-filtered coordinate fibers, not arbitrary affine
interpolation fibers.

Follow-up: `LineListAppearanceFiber.lean` now defines `appearingCoordinateAgreementFiber`, the
intersection of a coordinate fiber with `lineAppearingCodewords`.  It proves the same zero-stratum
cover, cardinal union bound, and punctured-budget consumer for these appearance-filtered fibers.
This does not prove a saving, but it moves the next proof obligation to the right object.

Follow-up: the appearance-filtered route now has its own arithmetic socket,
`ZeroAppearingCoordinateFiberBudgetFits` / `UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits`,
plus raw-to-appearance bridge lemmas.  The old coordinate-fiber fit is only a fallback; a positive
route can now plug in a genuinely smaller appearance-count envelope without being forced through
the refuted field-power arithmetic.

Follow-up: the appearance-filtered API now reaches the full line-list production wrapper via
`uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_appearingCoordinateFibers`.  Its
scanner forms show that, after the support-eligible line-list theorem, support arithmetic, and
appearance-fit arithmetic are fixed, any failed uniform bad-scalar budget must be either
zero-direction saturation or an overfull large-zero safe appearance fiber; with the high range
`M(t) >= 1`, the latter is forced into the low range `t < k`.

Follow-up: `Frontier/PowMapFiberCard.lean` records the finite-set constant-fiber regrouping lemma
behind the complete power-map lift.  It isolates the no-go mechanism for Deligne-style complete
sum lifts: the exact regrouping is elementary, but the complete source sum inherits the high
degree of the power map.  The finite commutative group form removes the supplied fiber hypothesis,
and the cyclic form identifies the multiplicity as `gcd(#G,e)`.

Follow-up: added `docs/kb/deltastar-464-bounded-complexity-powmap-2026-06-26.md`, tying the local
PDF check, the pow-map regrouping brick, and the appearance-filtered line-list replacement into one
bounded-complexity critique.  Verdict: interface progress only; the floor still needs global stack
domination or the thin-subgroup Paley/BGK sup bound.

## [2026-06-26] refine | floor successor propagation gate

Added:

- `docs/kb/deltastar-464-floor-successor-propagation-gate-2026-06-26.md`

and updated `_FloorClosureContract.lean` with scanner-facing negative forms for the uniform singleton
floor list and the successor step.  Uniform candidate-list exactness now fails exactly by a dyadic
rung `a >= 4` where exactness fails.  The successor theorem fails exactly by an adjacent pair where
`CandidateListExactAt a` holds but `CandidateListExactAt (a + 1)` does not.  This keeps the finite
`a = 4,5` floor evidence honest: it is useful only with a real successor theorem, or refutable by an
adjacent-rung counterexample.

Follow-up: `_AssaultV2_FloorLocalizationN32.lean` now exposes the finite split-prime mismatch
witnesses directly: a missing true floor-bad prime, a spurious listed prime, a uniform
least-prime-characterization mismatch, or a least split prime that is not below prize scale.

Follow-up: `_FloorClosureContract.lean` now also names the sharp one-representative certificate
`FamilyContainsBudgetedGlobalMax` and field-level wrapper `FloorClosureBudgetedMaxAtField`.  One
listed representative that is both within budget and globally worst is enough for
`WorstCaseIncidenceBounded`; failure says every proposed representative is either above budget or
beaten by another stack.

Follow-up: `LineListIncidenceMultiplicity.lean` now records the exact bipartite incidence graph
between bad scalars and witnessing codewords.  The first and second projections recover
`lineBadScalars` and `lineAppearingCodewords`, while the incidence cardinality decomposes as a sum
over either bad-scalar witness multiplicities or per-codeword heavy-scalar counts.  Consequently a
new conditional socket is available: if every bad scalar has at least `R` codeword witnesses, then
`#badScalars * R <= puncturedZeroStratifiedLineWeight`.  This is interface progress only; the
remaining hard input is a real multiplicity floor, or a sparse-witness counterexample.

Follow-up: `LineListIncidenceMultiplicity.lean` now pins the first multiplicity threshold exactly:
the `R = 1` floor is automatic, while failure of the `R = 2` floor is equivalent to a bad scalar
with a unique witnessing codeword.  Any nontrivial multiplicity-discount route must therefore
prove no unique-witness bad scalar exists on the relevant hard lines, or exhibit one as a refuter.
The no-unique-witness branch is now also named as `NoUniqueBadScalarWitness`, equivalent to the
`R = 2` multiplicity floor, and plugged into a factor-two bad-scalar budget consumer.

Follow-up: the factor-two multiplicity route is now scanner-facing at the codeword level:
`IsUniqueBadScalarWitnessCodeword` turns the singleton witness fiber into an actual unique codeword,
and `exists_uniqueWitnessCodeword_of_not_lineBadScalars_card_le` extracts that codeword from any
failed half-weight bad-scalar budget.  The uniform large-zero safe wrapper packages this as a
support-eligible branch plus no-unique-witness half-weight branch; it is still a conditional route,
not a floor proof.

Follow-up: `LineListIncidenceMultiplicity.lean` now has the positive equivalent of the
no-unique-witness condition: `BadScalarSecondWitnessProperty` says every witness to every bad
scalar has a distinct second witness, and
`noUniqueBadScalarWitness_iff_secondWitnessProperty` proves it is exactly the `R = 2` floor socket.
The factor-two discount can now be consumed through either the negative no-unique condition or this
constructive second-witness obligation.

Follow-up: the second-witness route is now fenced by unique decoding:
`badScalarWitnessCodewords_card_eq_one_of_uniqueDecoding` shows that in the strict half-distance
regime any bad scalar has a singleton witness fiber.  Consequently
`not_secondWitnessProperty_of_nonempty_uniqueDecoding` refutes the constructive route whenever the
bad-scalar set is nonempty and pairwise codeword distance supplies the Johnson unique-decoding
inequality.  This prevents misusing multiplicity in the ordinary unique-decoding zone.

Follow-up: `LineListIncidenceMultiplicity.lean` also has a quantitative singleton-defect fallback.
`singletonBadScalarDefect` counts bad scalars with a singleton witness fiber, and the new defect
bound proves `2 * #badScalars <= puncturedZeroStratifiedLineWeight + singletonBadScalarDefect`.
Thus the factor-two route can be weakened from "no singleton witnesses" to a combined arithmetic
budget on punctured weight plus singleton defect, with scanners for both defect-budget failure and
a concrete witness without a second witness.  Companion note:
`docs/kb/deltastar-464-singleton-defect-2026-06-26.md`.

Follow-up: the singleton defect endpoints are now exact.  Zero singleton defect is equivalent to
`NoUniqueBadScalarWitness` and to the constructive second-witness property; positive defect is
equivalent to an explicitly unique witness codeword; and
`UniformLargeZeroSafeSingletonDefectZero` packages the zero-defect condition on the large-zero safe
branch.  Strict Johnson unique decoding makes the singleton defect equal the full bad-scalar count,
so the defect route is a possible beyond-unique-decoding sparseness problem, not an improvement in
the ordinary unique-decoding zone.

Follow-up: `LineListSingletonDefectGeometry.lean` now turns singleton defects into their own
filtered incidence graph and slices them by exact zero-direction agreement set.  Each exact-profile
slice is bounded by the corresponding exact appearance fiber times the moving-support denominator,
so singleton-defect estimates can be attacked profile-by-profile rather than only globally.

Follow-up: the exact-profile singleton route now has a production-grade budget interface.
`ZeroExactSingletonDefectProfileBudgeted` bounds each exact zero-agreement singleton slice by
`D t`, yielding `singletonBadScalarDefect <= sum choose(#zeroSet,u1,t) * D t`; the matching
uniform wrapper consumes
`puncturedZeroStratifiedLineWeight + sum choose(#zeroSet,u1,t) * D t <= 2B`.  The converse scanner
returns a large-zero safe line where that combined profile arithmetic fails.

Follow-up: the exact-profile singleton cover now has an exact-appearance-fiber front door.
`ZeroExactAppearanceFiberSingletonBudgeted` asks for
`#exactAppearingFiber(S) * support/(a-t) <= D t`, which implies the singleton profile budget and
feeds the production wrappers.  New scanners return either an overfull singleton profile or an
overfull exact appearance profile when the aggregate uniform budget fails despite fixed support,
zero-safety, and profile arithmetic.

Follow-up: singleton defects now also have a codeword-indexed partition.  The sets
`codewordSingletonWitnessScalars` are disjoint over appearing codewords, their `biUnion` is exactly
`singletonBadScalars`, and `singletonBadScalarDefect` is the corresponding sum.  A per-codeword
budget therefore bounds the whole defect by `#lineAppearingCodewords * B`; the production wrappers
can consume either that appearing-codeword count or a `LineListBudgeted` cap to prove the final
bad-scalar budget from a combined weight-plus-singleton-cap inequality.

Follow-up: `LineListIncidenceMultiplicity.lean` now has the uniform converse scanner
`exists_largeZero_safe_uniqueWitnessCodeword_of_not_uniformLineBadScalarsBudgeted`.  Once the
support branch, support arithmetic, zero-direction safety, and half-weight arithmetic are fixed,
any failed uniform bad-scalar budget must exhibit a large-zero safe line with a bad scalar and its
unique witnessing codeword.  This makes the factor-two route refutable at the same production layer
where it is consumed.

Follow-up: the constructive second-witness socket now reaches the same production layer through
`UniformLargeZeroSafeSecondWitnessProperty`,
`uniformLineBadScalarsBudgeted_of_supportAdjusted_and_secondWitnessWeightDivTwo`, and the scanner
`exists_largeZero_safe_witness_without_second_of_not_uniformLineBadScalarsBudgeted`.  This lets a
future proof state the hard branch as "construct a distinct second witness for each bad-scalar
witness" and lets a failed production budget return the exact witness with no such second witness.

Follow-up: `SumsetExtremalityGuard.lean` records the corrected guarded form of the
sumset-extremality reduction.  A selected representative family proves the open-core incidence
budget only after a real split: domination on the guarded branch plus a separate budget for the
complement.  The file also adds exact scanner forms: failed guarded budget, failed guarded
extremality, and failed `WorstCaseIncidenceBounded` are all exposed as explicit counterexamples;
with the selected family budgeted, any full-budget failure is either an outside-guard over-budget
stack or a guarded stack that strictly beats every selected representative.  The same consumers
and scanners are packaged for explicit finite catalogues (`Finset` representative lists), matching
the probe-facing workflow.

Follow-up: `SumsetExtremalityGuard.lean` now also supports finite guard covers.  Instead of one
global guard and one catalogue, a proof may cover stack space by guard cells `G s`, give each cell
its own finite representative list `R s`, and plug the cover into `WorstCaseIncidenceBounded` and
the conditional `mcaDeltaStar` pin.  The failure scanner localizes a failed budget to either an
outside over-budget stack or a specific guard cell containing a stack that beats every listed
representative for that cell.

Follow-up: `LineListAppearanceFiber.lean` now also has exact zero-agreement appearance fibers.
The previous appearance-coordinate object covered a `t`-stratum by all zero-subsets; the exact
fiber requires `directionZeroAgreementSet(c,u0,u1) = S`, so the stratum cardinality is an exact
sum over `S` in `powersetCard t`.  This removes a cover looseness while preserving the same
punctured-budget consumer, but it still leaves the substantive exact-fiber bound open.

Follow-up: `LineListSingletonDefectGeometry.lean` now localizes exact singleton-profile failures to
the low interpolation range.  RS uniqueness bounds every exact appearing fiber by one when
`k <= t`, and the singleton incidence slice then inherits the support-denominator cap.  With that
cap below `D t` on high levels, the scanners return only overfull exact singleton or exact
appearance profiles with `t < k`.

Follow-up: the exact singleton-profile split is now an equality on zero-safe lines.  The singleton
incidence graph is exactly the biUnion of exact zero-agreement profile slices, and
`singletonBadScalarDefect` is the corresponding double sum.  The profile budget therefore has no
overlap slack: bounding each exact slice by `D t` is precisely a disjoint partition estimate before
the binomial summation.

Follow-up: the low exact singleton-profile scanners now have full failure split wrappers.  Without
assuming zero-direction safety up front, a failed uniform bad-scalar budget exposes either a
zero-direction saturating codeword or a large-zero safe low exact singleton/exact appearance profile
with `t < k`.

Follow-up: `LineListAppearanceFiber.lean` now owns the exact appearance-fiber production route.
`uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_exactAppearingFibers` consumes exact
zero-agreement appearance-fiber budgets directly, and the scanner
`unsafe_or_largeZero_safe_low_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted` localizes
failed uniform budgets to zero-direction saturation or a large-zero safe low exact appearance fiber.

Follow-up: `LineListSingletonDefectGeometry.lean` now exposes the raw MDS barrier for the exact
singleton route.  Exact appearance profiles and exact singleton-defect slices are bounded by
`|F|^(k-t) * support/(a-t)`, and the new scanners localize failed budgets to low profiles where the
proposed `D t` falls below that raw interpolation term.  The matching consumer proves that, if this
weighted raw envelope is already below `D t`, the exact singleton-profile production wrapper can use
it directly.  The lesson is precise: the singleton route must improve the low exact-appearance
envelope, not just reuse the field-power coordinate fiber.

Follow-up: the same singleton file now packages the positive raw-envelope baseline through
`zeroExactAppearanceFiberSingletonBudgeted_of_rawFieldPowBudget`,
`zeroExactSingletonDefectProfileBudgeted_of_rawFieldPowBudget`, and
`uniformLineBadScalarsBudgeted_of_rawFieldPowSingletonBudget`.  This proves the exact singleton
interface can consume the raw weighted MDS envelope, while keeping that envelope as the control
case rather than the desired improvement.  The split form
`uniformLineBadScalarsBudgeted_of_lowRawFieldPow_highSupportSingletonBudget` uses the raw term only
for low profiles `t < k` and the singleton support-denominator cap for high profiles.

Follow-up: the raw-envelope baseline now has a direct production-layer converse:
`exists_largeZero_safe_rawFieldPowSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted`
and `unsafe_or_largeZero_safe_rawFieldPowSingletonBudgetFailure_of_not_budgeted`.  Failed uniform
production exposes either zero-direction saturation or a large-zero safe stratum where the raw
weighted field-power envelope is already above `D t`.

Follow-up: the split raw/high-support certificate now has matching converse scanners:
`exists_lowRaw_or_highSupportFailure_of_not_budgeted` and
`unsafe_or_lowRaw_or_highSupportFailure_of_not_budgeted`.  Failed production is exactly separated
into zero-direction saturation, a low `t < k` raw field-power overrun, or a high `k <= t`
support-denominator overrun.

Follow-up: `LineListSingletonArithmeticObstruction.lean` records the raw exact-singleton arithmetic
no-go.  The combined `puncturedWeight + profile <= 2B` budget contains each raw weighted singleton
summand; if `D` dominates `|F|^(k-t) * support/(a-t)`, any summand above `2B` refutes the route.
In the common `2a <= n` range the `t = 0` direction already rules out any target with
`2B < |F|^k`, so the raw exact-singleton envelope is only a baseline obstruction.

Follow-up: `_RefinedProfileFloorBridge.lean` now specializes Linnik/TZ field-certificate failures
to used fine-profile labels.  After exact singleton candidate lists and Linnik/TZ field supply kill
the arithmetic floor-bad branch, a failed refined-profile field certificate returns either an
above-budget used representative or a beating stack for each used fine-profile representative.

Follow-up: the raw exact-singleton no-go now exposes its concrete scanner surface:
`exists_rawFieldPowSingletonProfileBudget_term_gt_of_two_mul_le` gives the explicit `t = 0`
weighted summand above `2B`, and
`unsafe_or_not_uniformWeightPlusExactSingletonProfileBudgeted_rawFieldPow_of_two_mul_le` removes
the zero-safety assumption by returning either zero-direction saturation or failure of the combined
exact singleton-profile budget.
The companion `fieldPow_le_two_mul_of_lowRawSingletonBudget` and
`not_uniformWeightPlusExactSingletonProfileBudgeted_lowRaw_of_two_mul_le` show the split
low-raw/high-support certificate cannot avoid this obstruction: for `0 < k` and `2a <= n`, `t = 0`
is already low and forces `|F|^k <= 2B` under any combined profile budget.

Follow-up: `LineListSupportRatioFiber.lean` exposes the first non-raw exact-appearance target.
Every appearing codeword has a support-ratio fiber of size at least `a - t`, where `t` is its exact
zero-direction agreement count; therefore exact appearance fibers are contained in coordinate
fibers whose support-ratio map has a heavy fiber.  The new scanner localizes failed production to
zero-direction saturation or a large-zero safe low support-ratio-heavy coordinate fiber.

Follow-up: the support-ratio-heavy target now has an explicit finite cover.  For each zero profile
`S`, `supportRatioLineFiberCover` chooses a heavy scalar `γ` and an `(a - #S)`-element moving
subfiber `T`, then covers by the ordinary coordinate-agreement fiber for `u0 + γ*u1` on `S ∪ T`.
The next positive estimate is therefore a concrete improvement over the crude union-bound sum
recorded by `supportRatioLineFiberCover_card_le_sum_coordinateAgreementFibers`.

Follow-up: the support-ratio line-fiber cover is exact on zero profiles, and the first reusable
non-raw envelope is now formalized.  Under `k <= a`, each `(γ, T)` cover fiber has at most one RS
codeword, yielding
`supportRatioHeavyCoordinateFiber_card_le_field_card_mul_choose` and the per-line budget
`zeroSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose`.
The coarser `supportRatioHeavyCoordinateFiber_card_le_field_card_mul_choose_n` replaces the moving
support size by `n` for line-independent arithmetic envelopes.
The finite cover sum is also a first-class route via `ZeroSupportRatioCoverSumBudgeted`,
`uniformLineBadScalarsBudgeted_of_supportRatioCoverSums`, and
`unsafe_or_largeZero_safe_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted`.
The direct ambient-binomial consumer is
`uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_lineFiberCoverChoose_n`; conversely,
failed production under the support and zero-safety hypotheses refutes that arithmetic fit through
`not_lineFiberCoverChooseBudgetFits_of_not_uniformLineBadScalarsBudgeted`.

Follow-up: `LineListSupportRatioArithmeticObstruction.lean` records the arithmetic caveat for the
ambient support-ratio envelope, while `LineListSupportRatioFiber.lean` now exposes the concrete
sum and single-term scanners for that envelope.  The fit with
`M(t) = |F| * choose(n, a - t)` contains every individual weighted profile term; if a possible
direction has `z` zeros and enough moving support for profile `t`, it forces
`choose(z, t) * |F| * choose(n, a - t) <= B`, with the `t = 0`, `z = a` case giving the familiar
`|F| * choose(n, a) <= B` obstruction in the `2a <= n` range.  Hence the ambient-binomial cover is
a baseline/control envelope; a floor proof must improve the finite cover sum before collapsing to
this bound.

Follow-up: the finite support-ratio cover-sum budget now has its direct scalar-times-binomial
control case and exact failure forms.  `supportRatioCoverSum_le_field_card_mul_choose`,
`zeroSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose_n`, and
`uniformLargeZeroSafeSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose_n` name the baseline
before collapsing to the ambient arithmetic obstruction; the failure forms
`not_zeroSupportRatioCoverSumBudgeted_iff_exists_coverSum_gt` and
`not_uniformLargeZeroSafeSupportRatioCoverSumBudgeted_iff_exists_coverSum_gt` expose a specific
overfull large-zero safe line, zero profile `S`, and finite `(γ, T)` cover sum before any ambient
scalar-times-binomial collapse.

Follow-up: `LineListIncidenceMultiplicity.lean` now has a per-codeword singleton-cap route in
addition to the total singleton-defect fallback.  A uniform cap on
`codewordSingletonWitnessScalars` plus either the actual appearing-codeword count or a
large-zero-safe line-list cap feeds the same factor-two production wrapper, and the scanners split
failed production into arithmetic-budget failure versus a concrete appearing codeword whose
singleton-witness scalar fiber exceeds the proposed cap.

Follow-up: the singleton-defect route now has uniform per-codeword singleton-cap wrappers.
`UniformLargeZeroSafeCodewordSingletonBudgeted` controls the number of singleton bad scalars
uniquely witnessed by each appearing codeword; production can use either the actual appearing count
or a separate large-zero-safe `LineListBudgeted` cap.  The matching scanners return either combined
arithmetic failure or a concrete appearing codeword whose singleton-witness scalar fiber exceeds
the proposed cap.

Follow-up: the per-codeword singleton route now has exact failure forms and combined scanners.
`not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt` and
`not_uniformLargeZeroSafeLineListBudgeted_iff_exists_lineAppearing_gt` expose the two missing
uniform caps directly.  The route-level scanners then split failed production into a finite
checklist: combined arithmetic failure, large-zero-safe line-list cap failure, or a concrete
appearing codeword with too many uniquely witnessed singleton scalars.

Essay: `deltastar-464-singleton-cap-route-critique-2026-06-26.md` records the current verdict on
this attack.  The new scanner is useful because it returns a finite line/codeword/scalar
counterexample, but it does not prove the floor until a support-ratio overlap-multiplicity theorem
bounds `codewordSingletonWitnessScalars` uniformly or a domination theorem lifts the local route to
the worst-stack MCA bound.

Follow-up: the per-codeword singleton-cap route now has its baseline support-denominator
obstruction.  `codewordSingletonWitnessScalars` is contained in `codewordHeavyScalars`, so on
zero-safe lines it is bounded by `support(u1)/(a - #zeroAgreement(c))`.  Consequently
`exists_largeZero_safe_codewordSingletonRouteSupportDivFailure_of_not_uniformLineBadScalarsBudgeted`
says a failed singleton-cap production attempt yields either combined arithmetic failure or a
concrete appearing codeword whose ordinary support-denominator capacity already exceeds the cap.

Follow-up: the support-ratio cover-sum route now feeds the singleton-defect profile route directly.
`uniformLineBadScalarsBudgeted_of_supportRatioCoverSumSingletonBudget` turns a finite cover-sum
envelope `M` plus the multiplier arithmetic `M(t) * support/(a-t) <= D(t)` into the exact
singleton-profile production wrapper.  The matching scanners expose either an overfull finite
`(gamma, T)` cover sum or the large-zero safe profile where that moving-support multiplier breaks.

Follow-up: `LineListCodewordSingletonSupportRatio.lean` now formalizes the codeword-indexed
support-ratio singleton cover proposed by the singleton-cap critique.  The projection theorem
`codewordSingletonWitnessScalars_eq_image_fst_supportRatioCover` and fiber cardinality theorem
`codewordSingletonSupportRatioCover_fst_fiber_card_eq_choose` package each singleton scalar for a
fixed codeword as a finite family of moving-support subfibers.  The new uniform cover cap feeds
the existing per-codeword singleton production route, and its scanner exposes either the usual
combined arithmetic failure or one overfull codeword-indexed support-ratio cover.  The next hard
target is still an overlap-multiplicity theorem that beats the resulting raw cover count.

Essay: `deltastar-464-codeword-ratio-overlap-no-go-2026-06-26.md` records the next critique.
For one fixed codeword, support-ratio fibers for distinct singleton scalars are disjoint, so
coordinate overlap inside the codeword-indexed cover is exhausted and recovers only the old
support-denominator bound.  Any remaining saving must use RS interpolation rigidity or the
second-witness/uniqueness condition, not raw moving-coordinate overlap.

Follow-up: the codeword-indexed cover now has its ambient scalar-times-binomial control envelope.
`supportRatioFiber_card_le_directionSupportSet_card` gives
`codewordSingletonSupportRatioCover_card_le_field_card_mul_choose`, and
`exists_largeZero_safe_codewordSupportRatioCoverFieldChoose_gt_of_not_coverBudgeted` records that
a failed uniform cover cap already beats `|F| * choose(#support(u1), a - #zeroAgreement(c))` on a
specific large-zero safe line and appearing codeword.  This is a baseline obstruction, not a floor
proof; the live target remains overlap saving inside the `(gamma,T)` cover.

Correction/refinement: the pure coordinate-packing side of that cover is sharper than the
scalar-times-binomial fallback.  `codewordSingletonSupportRatioCover_snd_injOn` proves that when
`a - #zeroAgreement(c) > 0`, the selected nonempty `T` determines `gamma`; hence
`codewordSingletonSupportRatioCover_card_le_support_choose` injects the cover into
`powersetCard support (a - #zeroAgreement(c))`.  This exhausts fixed-codeword coordinate overlap:
the remaining possible saving must be scalar-level RS interpolation rigidity or a second-witness
argument, not reuse of moving coordinates.  The support-choose consumer/scanner pair
`uniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted_of_supportChoose` and
`exists_largeZero_safe_codewordSupportRatioCoverChoose_gt_of_not_coverBudgeted`, together with
`exists_largeZero_safe_codewordSupportChooseRouteFailure_of_not_budgeted`, make this the active
baseline cap and production failure witness.

Follow-up: `LineListCodewordSingletonSupportRatio.lean` now exposes the scalar-level graph
interface that the last critique asked for.  `scalarRelationIndependent`,
`UniformLargeZeroSafeCodewordSingletonRelationForbidden`, and
`UniformLargeZeroSafeCodewordRelationIndependenceBudgeted` split any future interpolation graph
into two honest obligations: singleton scalars contain no relation edge, and the relation has no
large independent set.  The consumer
`uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationIndependence` plugs those
obligations into the existing singleton-cap production route.  The scanner
`exists_largeZero_safe_codewordRelationIndependentRouteFailure_of_not_budgeted` says failed
production yields either the usual arithmetic failure or a concrete overlarge independent set of
singleton scalars for one appearing codeword.  Companion note:
`deltastar-464-singleton-independence-graph-2026-06-26.md`.

Follow-up: the singleton-scalar graph interface now has the weaker witness-local independence
budget `UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted`.  It only asks to bound
independent subsets of the actual `codewordSingletonWitnessScalars` fiber, while the earlier
global budget remains a sufficient shortcut via
`uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationIndependence`.  The
new consumer and scanner,
`uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationWitnessIndependence` and
`exists_largeZero_safe_codewordRelationWitnessIndependentRouteFailure_of_not_budgeted`, make the
next graph target narrower and more honest.

Follow-up: the scalar graph route now has exact forbidden-edge failure forms.
`not_scalarRelationIndependent_iff_exists_edge` and
`not_uniformLargeZeroSafeCodewordSingletonRelationForbidden_iff_exists_edge` turn a failed
forbidden-edge theorem into two distinct singleton scalars connected by the proposed relation.
The full scanner
`exists_largeZero_safe_codewordRelationWitnessRouteObstruction_of_not_budgeted` no longer assumes
the forbidden half: failed production yields either such an edge, the usual arithmetic failure, or
an over-cap independent subset of the singleton-witness fiber.

Follow-up: `LineListCodewordSupportChooseArithmeticObstruction.lean` now names the arithmetic
obstruction for that support-choose baseline.  A uniform support-choose budget contains every
concrete term `choose(#support(u1), a - #zeroAgreement(c,u0,u1))`; conversely an exact profile or
support-lower-bound profile with `S < choose(s, a-z)` refutes the budget.  The route-level scanner
now has a profile form,
`exists_largeZero_safe_codewordSupportChooseRouteProfileFailure_of_not_budgeted`, returning the
usual combined arithmetic failure or an appearing codeword with explicit `(support, zeroAgreement)`
data whose binomial term is already over cap.

Follow-up: the support-choose baseline is now compared directly to the old denominator scalar cap.
`support_div_le_choose_of_pos_le` proves the elementary arithmetic comparison, and
`codewordSingletonWitnessScalars_card_le_support_choose_via_denominator` records that on every
zero-safe appearing codeword the denominator route already bounds singleton-witness scalars by the
support-choose term.  This pins support-choose as cover control and obstruction localization, not
by itself a scalar-level improvement toward the floor.

Essay: `deltastar-464-weighted-support-choose-route-2026-06-26.md` records the next refinement.
The uniform support-choose cap paid `#appearingCodewords * S`; the new
`codewordSupportChooseWeight` pays
`sum_c choose(#support(u1), a - #zeroAgreement(c))` over actual appearing codewords.  Lean now
proves `singletonBadScalarDefect_le_codewordSupportChooseWeight_of_zeroSafe`, consumes the budget
via `uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportChooseWeightBudget`, and
scans failed production with
`exists_largeZero_safe_codewordSupportChooseWeight_gt_of_not_uniformLineBadScalarsBudgeted`.  This
is a real accounting refinement but still spends only coordinate-packing information; the next
nonredundant target remains profile concentration or scalar-level second-witness rigidity.

Follow-up: two naive singleton graph candidates are now formally refuted.  The coordinate-overlap
relation `supportRatioFiberOverlapRelation` has no distinct-scalar edges for one fixed codeword,
so `uniformRelationWitnessIndependenceBudgeted_supportRatioFiberOverlap_iff_singletonBudgeted`
shows its witness-local graph budget is exactly the original singleton cap.  The endpoint
second-witness relation in `LineListCodewordSingletonSecondWitnessRelation.lean` is also vacuous
on singleton witnesses, with
`endpointSecondWitnessRelationWitnessBudgeted_iff_codewordSingletonBudgeted` proving the same
collapse.  Essay: `deltastar-464-graph-candidates-refuted-2026-06-26.md`.

Follow-up: `LineListCodewordSingletonSupportDivWeight.lean` now has the scalar-sharper weighted
denominator route.  `codewordSupportDivWeight` pays the actual
`#support(u1)/(a - #zeroAgreement(c))` cap for each appearing codeword, and
`singletonBadScalarDefect_le_codewordSupportDivWeight_of_zeroSafe` feeds the same factor-two
production wrapper through
`uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportDivWeightBudget`.  The
scanner `exists_largeZero_safe_codewordSupportDivWeight_gt_of_not_uniformLineBadScalarsBudgeted`
returns the smaller denominator-weight obstruction, while
`codewordSupportDivWeight_le_codewordSupportChooseWeight_of_zeroSafe` records that weighted
support-choose only implies this baseline.  Companion note:
`deltastar-464-weighted-denominator-baseline-2026-06-26.md`.

Follow-up: `LineListCodewordSupportDivArithmeticObstruction.lean` gives the denominator baseline
its one-term arithmetic no-go surface.  `codewordSupportDivWeight_term_le` bounds every concrete
appearing-codeword denominator term by the weighted sum, and the three refuters
`not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_term_gt`,
`not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_profile_term_gt`, and
`not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_support_lower_term_gt`
turn explicit support/zero-agreement profiles into failure of the uniform weighted denominator
budget.  This is one-way certification, not a claim that every failed sum has a single bad term.
Companion note:
`deltastar-464-weighted-denominator-term-obstruction-2026-06-26.md`.

Follow-up: the singleton graph interface now records the generic forbidden-edge collapse.
`relationWitnessIndependenceBudgeted_iff_codewordSingletonBudgeted_of_forbidden`
says that once singleton witnesses are independent for a proposed relation, the witness-local
independence budget is equivalent as a theorem statement to the original per-codeword singleton
cap.  The companion failure iff
`not_relationWitnessIndependenceBudgeted_iff_exists_singleton_card_gt_of_forbidden`
returns exactly the old overfull singleton fiber under forbidden edges.  This keeps future graph
attempts honest: the relation can be a proof method, but the witness-local formulation is not a
weaker target.

Follow-up: `LineListCodewordSingletonRelationColorCover.lean` adds a bounded-invariant route into
the clique-cover certificate.  `scalarRelationColorForcesEdges` says equal colors force relation
edges on the singleton-witness fiber; `scalarRelationCliqueCover_of_colorForcesEdges` turns color
fibers into cliques; and
`uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationColorBudgeted` plugs a
uniform color-image bound into the witness-local graph budget.

Follow-up: `LineListCodewordSingletonRelationCliqueCover.lean` adds a positive certificate form
for the graph route.  `scalarRelationIndependent_card_le_of_cliqueCover` proves that an
independent singleton set meets each relation clique at most once, and
`UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted` packages the uniform witness-local
cover obligation.  The scanner
`exists_largeZero_safe_codewordRelationCliqueCoverRouteObstruction_of_not_budgeted` returns an
actual forbidden edge, the usual arithmetic failure, or a singleton fiber with no at-most-`S`
relation-clique cover.  This gives future interpolation relations a finite certificate target.

Follow-up: `LineListCodewordSingletonRelationColorCover.lean` turns that finite certificate into
a bounded-invariant target.  `scalarRelationCliqueCover_of_colorForcesEdges` proves that if equal
color values inside a singleton scalar set force relation edges, then the color fibers form a
clique cover.  The uniform wrapper
`UniformLargeZeroSafeCodewordRelationColorBudgeted` asks for at most `S` color values on each
actual singleton-witness fiber plus the equal-color edge theorem.  This is still only a proof
method: the missing object is a nontrivial interpolation or exceptional-pencil invariant with a
small image.

Follow-up: the color-cover route now has exact failure scanners.
`scalarRelationColorFailure` packages the two local obstructions: too many colors on the fiber,
or a same-color pair that is not related.  The uniform iff
`not_uniformLargeZeroSafeCodewordRelationColorBudgeted_iff_exists_colorFailure` and scanner
`exists_largeZero_safe_codewordRelationColorRouteObstruction_of_not_budgeted` expose finite
witnesses for any proposed invariant: a forbidden relation edge, the usual arithmetic failure, or
a concrete color-certificate failure.

Follow-up: the color-cover route now has the generic injectivity collapse.  If the singleton
relation is forbidden on true singleton witnesses and a color really forces relation edges, then
`scalarRelationColor_image_card_eq_of_independent_of_forcesEdges` makes the color image exactly as
large as the singleton fiber.  Uniformly,
`relationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden_of_forcesEdges` and its negated
form show that a fixed edge-forcing color certificate is equivalent to the original singleton cap.

Follow-up: `LineListCodewordSingletonRelationColorNoGo.lean` rules out the naive same-color
specialization of the color route.  `scalarRelationIndependent_sameColorRelation_iff_injOn`
identifies independence for `R gamma gamma' := chi gamma = chi gamma'` with injectivity of `chi`
on the finite scalar set, and
`sameColorRelationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden` shows that, under
forbidden same-color edges, the bounded-color certificate is exactly the original singleton
budget.  The companion failure theorem
`not_sameColorRelationColorBudgeted_iff_exists_singleton_card_gt_of_forbidden` returns exactly
the old overfull singleton fiber.  Companion note:
`deltastar-464-same-color-relation-no-go-2026-06-26.md`.

Follow-up: `LineListCodewordSingletonRelationCliqueCover.lean` now has the direct clique-cover
collapse.  `scalarRelationCliqueCover_singletons` builds a singleton cover from any direct
singleton cap, while `scalarRelationCliqueCover_card_ge_of_independent` shows an independent
ambient fiber needs at least one clique per vertex.  Uniformly,
`relationCliqueCoverBudgeted_iff_codewordSingletonBudgeted_of_forbidden` and
`not_relationCliqueCoverBudgeted_iff_exists_singleton_card_gt_of_forbidden` make the
clique-cover certificate equivalent to the original singleton budget under forbidden edges.
Companion note:
`deltastar-464-clique-cover-collapse-2026-06-26.md`.
