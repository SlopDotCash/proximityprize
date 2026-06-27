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

Follow-up: `LineListSupportRatioFiber.lean` now localizes explicit support-ratio cover-sum
failures to the low interpolation range once the high profiles are paid for.  The new theorem
`supportRatioCoverSum_le_field_card_mul_choose_of_k_le_card` bounds a high zero-profile cover sum
by `|F| * choose(#support(u1), a - t)`, and
`unsafe_or_largeZero_safe_low_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted` turns
failed production into either zero-direction saturation or a large-zero safe low cover-sum witness.
Companion note:
`deltastar-464-support-ratio-cover-sum-low-scanner-2026-06-26.md`.

Follow-up: `LineListCodewordSingletonRelationException.lean` adds the honest exceptional-set
variant of the singleton graph route.  Outside the classified exceptional set the relation must be
forbidden/independent, while the exceptional singleton scalars get their own budget.  Production
uses the cap `S + E`; scanners expose an outside edge, an overlarge good independent subset, the
usual arithmetic failure, or an overlarge exceptional residue.  Companion note:
`deltastar-464-exceptional-relation-route-2026-06-26.md`.

Follow-up: `LineListCodewordSingletonSupportOverlapRelation.lean` now refutes every relation whose
edges factor through fixed-codeword support-ratio fiber overlap.  Such subrelations have no
distinct-scalar edges, so their witness-local independence budget is equivalent to the original
singleton cap; the negated form returns the same overfull singleton fiber.  Companion note:
`deltastar-464-support-overlap-subrelation-no-go-2026-06-26.md`.

Follow-up: `Frontier/_FloorClosureContract.lean` now compares the old field closure certificate
with the sharp budgeted-global-max certificate.  `FloorClosureAtField` is exactly
`FloorClosureBudgetedMaxAtField` plus `FamilyBounded`; failure of the sharp certificate already
refutes the old contract, while the only extra old-style failure is an over-budget non-maximal
listed family member.

Follow-up: `LineListCodewordSingletonRelationException.lean` now exposes the relation-free
partition baseline behind the exceptional-set route.  Under outside-forbidden edges,
`UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted` is equivalent to directly bounding
`codewordSingletonWitnessScalars \ Xi`, and the direct partition theorem combines that
non-exceptional cap with the exceptional cap to recover the `S + E` singleton budget.  The
production scanner `exists_largeZero_safe_codewordPartitionRouteFailure_of_not_budgeted` returns
either the usual punctured-weight arithmetic failure or one appearing codeword where the
non-exceptional or exceptional side overruns its budget.

Follow-up: `Frontier/_FloorClosureContract.lean` now records the exhaustive-family endpoint:
`familyContainsBudgetedGlobalMax_univ_iff_worstCaseIncidenceBounded` and
`floorClosureBudgetedMaxAtField_univ_iff_floorGood_and_worstCaseIncidenceBounded`.  The all-stack
sharp certificate is just floor-goodness plus the original open-core incidence bound; the only
mathematical content in a smaller floor catalogue is proving that it still contains a budgeted
global maximizer.

Follow-up: `LineListSupportRatioFiber.lean` now has the positive half of the support-ratio
cover-sum low-profile split.  `ZeroLowSupportRatioCoverSumBudgeted` and
`UniformLargeZeroSafeLowSupportRatioCoverSumBudgeted` isolate the `t < k` obligations, while
`uniformLineBadScalarsBudgeted_of_lowSupportRatioCoverSums` combines those low estimates with the
high-profile scalar-times-support-binomial ceiling.  The matching negated iff exposes an overfull
low cover-sum witness exactly when the low-budget assumption fails.

Follow-up: the same file now mirrors that split for support-ratio-heavy coordinate fibers.
`ZeroLowSupportRatioHeavyCoordinateFiberBudgeted` isolates the low `t < k` heavy-fiber estimates;
`uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavyCoordFibers` combines them with the
high-profile RS-uniqueness ceiling `1 <= M t`; and
`exists_largeZero_safe_low_supportRatioHeavyCoordFiber_gt_of_not_budgeted` exposes the exact
zero-safe low-heavy obstruction under failed production.

Follow-up: the same support-ratio split now has a direct production converse:
`exists_largeZero_safe_low_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted` returns an
overfull large-zero safe low cover sum when support-side production, zero-direction safety,
arithmetic fit, and the high-profile cover-sum ceiling are fixed but the bad-scalar budget still
fails.

Follow-up: the support-ratio-heavy coordinate-fiber route now has the same positive low/high
production wrapper.  `uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavyCoordFibers` combines
low heavy-fiber bounds with the high-profile singleton ceiling, and
`exists_largeZero_safe_low_supportRatioHeavyCoordFiber_gt_of_not_budgeted` extracts a low heavy
fiber overflow from failed production under those fixed side hypotheses.

Follow-up: `Frontier/_ProfileFiberSlackDominance.lean` now adds the zero-slack profile cardinality
gate.  `BadCountInjectiveOn` names a finite scanner family with pairwise distinct bad-scalar
counts; if bad counts are constant on profile fibers, then `profile` is injective on that family
and `card_le_profileCard_of_profileBadCountFiberConstant_badCountInjectiveOn` forces
`U.card <= Fintype.card P`.  The negated forms refute zero-slack fiber constancy, representative
factorization, and zero oscillation whenever a proposed compressed profile has too few labels.
Companion note:
`deltastar-464-zero-slack-profile-cardinality-gate-2026-06-26.md`.

Follow-up: the same zero-slack cardinality gate now has a global bad-count-image form.
`StackBadCountImage` is the finite image of `StackBadCount` over all stacks, and
`stackBadCountImage_card_le_profileCard_of_profileBadCountFiberConstant` proves every zero-slack
profile needs at least that many labels.  The matching negated theorems refute fiber constancy,
representative bad-count factorization, and zero same-profile oscillation directly from
`Fintype.card P < (StackBadCountImage F C delta).card`.

Follow-up: the profile image gate now has a positive-slack cover form.
`ProfileBadCountImageCovered` asks each profile label to provide a finite set of allowed realized
bad-count values, and `stackBadCountImage_card_le_sum_profileBadCountCover` bounds the global
bad-count image by the sum of those cover sizes.  The negated theorem gives a finite refuter for
any interval/cover explanation whose total size is too small.

Follow-up: the cover gate is now instantiated for the existing same-profile oscillation certificate.
If representatives lie in their fibers, `ProfileFiberOscillationBounded` covers each profile's
bad-count values by the interval centered at the representative count with radius `slack p`.
`stackBadCountImage_card_le_sum_profileFiberOscillationIntervals` is the resulting image-size
pressure, and the negated theorem refutes oscillation certificates whose intervals are too small in
aggregate.

Follow-up: the interval cover now has summed-slack and uniform-slack corollaries.
`card_Icc_sub_add_le_two_mul_add_one` bounds each representative-centered count interval by
`2 * slack p + 1`, giving `stackBadCountImage_card_le_sum_profileFiberOscillationSlack` and
`stackBadCountImage_card_le_profileCard_mul_uniformOscillationSlack`.  The negated sockets refute
oscillation certificates from only a summed slack budget, or from profile count times a uniform
slack cap.

Follow-up: the summed-slack and uniform-slack image gates now have direct bundled-certificate
forms for `ProfileFiberOscillationCertificate`.  The certificate-level negated sockets refute the
full structured certificate when the bad-count image is too large for the advertised summed or
uniform slack budget, without separately unpacking the representative-in-fiber and oscillation
components.

Follow-up: the slack image gate now also covers the unstructured domination route.
`profileBadCountImageCovered_of_profileFiberSlackDominates` covers each profile by the one-sided
interval `[0, StackBadCount(rep p) + slack p]`, with
`not_profileFiberSlackDominates_of_sum_capIntervalCard_lt_stackBadCountImage` as the finite
refuter.  A full budgeted slack certificate forces the global bad-count image into `[0, B]`,
recorded by `stackBadCountImage_card_le_budget_add_one_of_profileFiberSlackCertificate` and the
matching certificate/field-closure refuters.

Follow-up: the KKH26 s=128 ceiling consumer now accepts the paper-facing square collision budget.
`card_collisionPairs` identifies the collision-resultant family as `A(A-1)` and
`card_collisionPairs_le_square` gives the coarse `A^2` estimate; the s=128 wrappers
`s128_supply_beats_budget_of_square_bound` and
`kkh26_mcaDeltaStar_le_s128_of_square_bound`, plus the named-PNT bridge
`kkh26_s128_ceiling_of_thornerZamanPNTinAP_square` and the regime-correct count wrapper
`kkh26_s128_of_polyModulusCount_square`, compose that estimate into the existing named
`TZPrimeSupply` / `ThornerZamanPNTinAP` consumers.  Companion note updated:
`wf407-B3-s128-thorner-zaman-ceiling.md`.

Follow-up: the Krawtchouk/MacWilliams LP-certificate route is now recorded as a domain-blind no-go.
`DelsarteLPNoGo.domainBlind_bound_transfers` shows that any invariant-only ceiling transfers across
same-invariant domains, while `domainBlind_counterexample_refutes` packages the matching
counterexample criterion.  Companion note:
`deltastar-464-krawtchouk-lp-certificate-verdict-2026-06-26.md`.

Follow-up: `CapacityBoundsAdmissible.lean` now exposes raw-bound
`FRSEpsMCACapacityGG25Frontier` wrappers for the direct order/inter-orbit, coset-separation, and
GR08 geometric folded-RS T4.14 routes.  The wrappers compose the existing `t <= 2 / eta`
frontiers with `FRSEpsMCACapacityGG25TLeFrontier.toFrontier`, so the raw `hBound` field is
derived by the checked arithmetic bridge rather than added as a new assumption.  Companion note:
`deltastar-464-folded-frs-capacity-route-pin-2026-06-26.md`.

## [2026-06-26] refute | convolution-squaring bootstrap start condition

Added:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_D1ConvolutionSquaringReduction.lean`
- `docs/kb/deltastar-464-convolution-squaring-bootstrap-verdict-2026-06-26.md`

to record that the arXiv:2606.24471 mirrored self-convolution bootstrap squares Fourier
concentration but, for the smooth-subgroup test `1_{μ_n}/n`, the starting concentration is exactly
`M(μ_n)/n`.  The iterated squared target is therefore equivalent to the original Paley house bound,
so D1 is a consumer of a Paley-strength input rather than an independent floor proof.

## [2026-06-26] reduce | fixed-r KKH26 s=128 square budget

Follow-up: the s=128 KKH26 consumer now exposes the sharper fixed-`r` resultant-size budget.
`KKH26TightCeiling.lean` proves the generic `log((2r)^(2^(μ-1)))` route plus the normalized
`tightResultantLog_eq` / `kkh26_mcaDeltaStar_le_of_TZ_tight_square_bound_log` form; the s=128
surface adds `s128_tightResultantLog_eq`, `kkh26_mcaDeltaStar_le_s128_tight_square_bound`, and
the normalized `kkh26_mcaDeltaStar_le_s128_tight_square_bound_log`.  The named Thorner-Zaman
bridge and AvD1 regime-correct count layer export matching tight-square consumers.  This relaxes
the bad-prime budget but does not remove the named polynomial-modulus prime-count input.

Follow-up: the s=128 named Thorner-Zaman bridge now has the canonical floor-supply wrapper
`kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log`, and the AvD1
regime-correct consumer exposes
`kkh26_s128_of_polyModulusCount_floor_tight_square_log`.  The bad-prime budget is compared
directly against `⌊tzDensityLB n β ε⌋₊`.

Follow-up: `_KKH26ThornerZamanTightBridge.lean` now exposes the same normalized tight square
budget without specializing to `s = 128`, composing the generic `ThornerZamanPNT` statement with
`kkh26_mcaDeltaStar_le_of_TZ_tight_square_bound_log` in real-bound, natural-floor, and canonical
`floor(tzDensityLB)` forms.

Follow-up: the generic floor-supply wrapper now has
`kkh26_ceiling_of_thornerZamanPNT_floor_tight_square_bound_log_auto_nonneg`.  Because the normalized
tight KKH budget is nonnegative under the existing `r >= 2` and `n^beta >= 2` hypotheses, a strict
comparison against `⌊tzDensityLB n beta eps⌋₊` already implies the density nonnegativity side
condition.

Follow-up: the s=128 bridge and AvD1 count layer expose the matching automatic-nonnegativity forms
`kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log_auto_nonneg` and
`kkh26_s128_of_polyModulusCount_floor_tight_square_log_auto_nonneg`.

## [2026-06-26] refute | Tsang high-moment range is constant-depth here

Added `_D3TsangHighMomentRangeGate.lean` and companion note
`deltastar-464-tsang-high-moment-range-gate-2026-06-26.md`.  The arXiv:2606.10242
Tsang/Soundararajan high-moment template is useful as a stress test, but its usable range is
range-limited.  The finite-field diagonal analogue `n^(2r) <= q` becomes `2r <= beta` at
`q = n^beta`, so fixed polynomial field size supplies only constant-depth control while the
prize needs Paley-saddle depth growing like `log q`.

## [2026-06-26] refute | MacMahon margin encoding without fiber budget

Added `_D4MacMahonMarginEncodingGate.lean` and companion note
`deltastar-464-macmahon-margin-encoding-gate-2026-06-26.md`.  The gate records that a
MacMahon/matrix-pair margin decomposition can transfer a prize bound only after supplying an
actual total margin-fiber budget, or a uniform fiber cap times a margin-count bound.  Coarse margin
support alone remains compatible with an arbitrarily large one-margin spike.

## [2026-06-26] reduce | permutation-insdel random-RS rank needs smooth transfer

Added `_D4PermutationInsdelRankTransferGate.lean` and companion note
`deltastar-464-permutation-insdel-rank-transfer-gate-2026-06-26.md`.  The arXiv:2606.22344
random-RS permutation/insdel rank method transfers to the prize only after a pointwise certificate:
either the fixed dyadic smooth domain lies in the generic-good locus, or every actual smooth-domain
extremal configuration is covered by the generic symbolic model.  The countermodels show generic
rank/SZ control alone remains compatible with a smooth-domain spike.

## [2026-06-26] refute | random-operator chaining without deterministic transfer

Added `_D5RandomOperatorChainingTransferGate.lean` and companion note
`deltastar-464-random-operator-chaining-transfer-gate-2026-06-26.md`.  The gate records that a
random multiplier/operator norm or generic-chaining theorem transfers to the fixed smooth-domain
period process only through pointwise domination or a genuine bad-event cover.  Without that
deterministic transfer, a bounded random model remains compatible with a smooth-domain spike.

## [2026-06-26] refute | homological vanishing without prime-field transfer

Added `_D0HomologicalVanishingTransferGate.lean` and companion note
`deltastar-464-homological-vanishing-transfer-gate-2026-06-26.md`.  The positive gate records the
exact pointwise pullback needed to turn a homological/function-field model bound into a prize-prime
bound.  The countermodels show that bounded auxiliary homological statistics, fixed-depth
vanishing, or a convexity-scale envelope remain compatible with prime-field spikes unless a
growing-depth prime comparison and budget improvement are supplied.

## [2026-06-26] route | non-Paley sweep and folded transfer threshold no-go

Added `deltastar-464-every-nonpaley-angle-2026-06-26.md`, filling the KB path named by the
latest issue sweep.  The note routes folded-RS/subspace-design capacity MCA to the existing
T4.13-backed FRS surfaces, routes Krawtchouk/LP and monodromy ideas to their existing no-go gates,
and records the honest plain-RS conclusion: adjacent-code wins do not prove the smooth-domain
floor without a new transfer theorem.  `FoldingTransferNoGo.lean` now names that simple transfer
shape as `PlainToFoldAgreementTransfer` / `UniversalPlainToFoldAgreementTransfer` and refutes every
nonzero folded threshold below the one-corruption-per-orbit plain-agreement witness via
`not_plainToFoldAgreementTransfer_of_A_le_N_mul_d_of_T_pos`.

## [2026-06-26] reduce | exact high-multiplicity weight decomposition

Added `deltastar-464-high-multiplicity-weight-decomposition-2026-06-26.md`,
`weightLine_add_mult_eq_weightE1_add_zeroE1Nonzero`,
`weightLine_le_imp_highMult_exact`, `badWeight_card_mul_le_exact`, and
`badWeight_empty_of_mult_cap_exact` in
`HighMultiplicityBadCount.lean`.  The new identity proves that, for each affine error line, line-word
weight plus root multiplicity equals `weight(e1)` plus the fixed `e1 = 0, e0 != 0` correction; the
exact bad-scalar bound retains that correction in the high-multiplicity threshold.  A future
ratio-function degree cap can close a fixed error line by proving
`D < weight(e1) + #{i : e1 i = 0 ∧ e0 i ≠ 0} - w`.  This removes a bookkeeping ambiguity in the
per-line count, but still leaves the global in-window codeword-pair/list supply as the open
sub-Johnson step.

## [2026-06-26] reduce | exact ratio-degree collapse for weight-bad polynomial lines

Added `deltastar-464-ratio-degree-exact-collapse-2026-06-26.md` and
`RatioMultiplicity.badWeight_empty_of_degree_exact`.  The theorem composes the exact
high-multiplicity cap gate with `mult_poly_le_max`: for polynomial error coordinates
`P(dom i), Q(dom i)`, the low-weight bad-scalar set is empty once
`max(deg P, deg Q) < #{Q ≠ 0 on dom} + #{Q = 0 ∧ P ≠ 0 on dom} - w`, assuming no scalar makes
`P + γQ` identically zero.  This closes the structured polynomial-line local case at the exact
threshold.  Follow-up in the same bridge: without the nondegeneracy hypothesis, the bad set is
contained in the degenerate scalar set `{γ : P + γQ = 0}`, and this set has size at most one when
`Q ≠ 0`.  The final structured-line package is an exact empty-or-singleton dichotomy:
`badWeight_eq_empty_or_singleton_of_degree_exact` and
`badWeight_card_eq_zero_or_one_of_degree_exact`, with
`badWeight_card_eq_one_iff_degenerate_exists_of_degree_exact` identifying the count-one branch
exactly with existence of a degenerate scalar.  Follow-up: `degenerate_exists_iff_scalarMultiple`
and its consumers rewrite that branch as the ordinary scalar-multiple condition `P = cQ`; under
`Q ≠ 0`, the structured low-weight set is empty iff `P` is not a scalar multiple of `Q`.  The
arbitrary-stack structural reduction remains open.

## [2026-06-26] refute | arbitrary ratio profiles block support-only caps

Added `deltastar-464-arbitrary-ratio-profile-obstruction-2026-06-26.md` and the
`RatioCensus.ratioSeq_negProfile_one` / `ratioMult_negProfile_one` /
`not_uniform_ratioMult_cap_of_fiber_gt` obstruction layer.  For any map `r : ι → F`, the
full-support line `s₁ ≡ 1`, `s₀ = -r` realizes that exact ratio profile, and its low-weight
incidence is the large-fibre count of `r`.  Follow-up theorems
`fiberLevel_subtypeProd_profile_eq` and `farIncidence_subtypeProd_profile_card_eq` show that any
nonempty finite set of bad scalars can be prescribed exactly with positive multiplicity.  Thus the
ratio-degree collapse cannot be promoted to arbitrary stacks by support counting alone; a floor
proof using this lane still needs polynomial domination or a global list-supply theorem.

## [2026-06-27] refute | one-spike profiles force numerator degree

Added `Frontier/RatioProfileDegreeObstruction.lean` and companion note
`deltastar-464-ratio-profile-degree-obstruction-2026-06-27.md`.  The theorem
`spike_profile_numerator_degree_ge` proves that a represented one-spike ratio profile over an
injective domain forces numerator degree at least `|ι| - 1`; the sparse variant
`sparse_profile_numerator_degree_ge` forces degree at least the complement size `|ι| - #support`.
This blocks any blanket reduction from arbitrary ratio profiles to uniformly bounded-degree
polynomial lines; the actual δ* floor still needs a structural domination theorem or a global
list-supply bound.

## [2026-06-27] reduce | support-degree scanner for sparse represented profiles

Extended `Frontier/RatioProfileDegreeObstruction.lean` with
`sparse_profile_support_card_add_natDegree_ge` and
`not_sparse_profile_of_support_card_add_natDegree_lt`.  The sparse ratio-profile obstruction is
now available in subtraction-free form: any represented nonzero profile supported on `S` satisfies
`|ι| <= #S + deg(P)`, so scanners can refute a proposed low-degree representation directly from
`#S + deg(P) < |ι|`.

## [2026-06-27] reduce | low/high appearance-fiber production wrappers

Extended `LineListAppearanceFiber.lean` with low-profile budget predicates and production
wrappers for both ordinary and exact appearance fibers.  Callers can now supply only the hard
low-range estimates `t < k`; the high range `k <= t < a` is discharged by RS uniqueness whenever
the envelope has `1 <= M t`.  This makes the remaining positive #464 line-list target exactly a
low appearance-fiber saving, not another high-stratum bookkeeping obligation.

## [2026-06-27] reduce | low appearance feeds low exact appearance

Added
`zeroLowExactAppearingZeroAgreementFiberBudgeted_of_lowAppearingCoordinateFiberBudgeted` and its
uniform version
`uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowAppearingBudgeted`.
Since exact zero-agreement appearance fibers sit inside the corresponding coarse
appearance-coordinate fibers, a single low-profile appearance estimate now feeds both the ordinary
and exact low/high production wrappers.  The same pass added exact negated forms for the low
appearance-coordinate and low exact appearance budgets:
`not_zeroLowAppearingCoordinateFiberBudgeted_iff_exists_low_fiber_gt`,
`not_uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_iff_exists_low_fiber_gt`,
`not_zeroLowExactAppearingZeroAgreementFiberBudgeted_iff_exists_low_fiber_gt`, and
`not_uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_iff_exists_low_fiber_gt`.
Per-line low-budget failure now unpacks to `t < k`, subset `S`, and strict overrun
`M t < #fiber(S)`; uniform failure additionally identifies the large-zero safe line carrying that
overrun.

Follow-up wrappers `not_zeroLowAppearingCoordinateFiberBudgeted_of_not_zeroLowExactAppearingBudgeted`
and `not_uniformLowAppearingBudgeted_of_not_uniformLowExactAppearingBudgeted` record the
contrapositive collapse: if the low exact appearance route fails, the coarser low
appearance-coordinate route already fails.  The exact socket is therefore a refinement, not an
independent residual.

Follow-up overrun converters
`exists_low_appearingCoordinateFiber_gt_of_exists_low_exactAppearingFiber_gt` and
`exists_uniformLow_appearingCoordinateFiber_gt_of_exists_uniformLow_exactAppearingFiber_gt`
make the witness-level collapse explicit: a strict low exact appearance-fiber overflow is already
a strict overflow for the coarser appearance-coordinate fiber, with the same `t < k` and subset
payload.

Follow-up direct scanners
`exists_largeZero_safe_low_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted` and
`exists_largeZero_safe_low_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted` cover the
common zero-safety-fixed production case: once support-side production, support arithmetic,
appearance-fiber arithmetic, and the high `M(t) >= 1` ceiling are fixed, failed bad-scalar
production directly returns a large-zero safe low overrun witness, without the unsafe disjunction.

## [2026-06-27] reduce | exact supersets cover coarse appearance fibers

Added
`appearingCoordinateAgreementFiber_subset_exactAppearingZeroAgreementFiber_superset_biUnion`
and
`appearingCoordinateAgreementFiber_card_le_sum_exactAppearingZeroAgreementFiber_supersets`.
For `S ⊆ directionZeroSet u1`, every coarse appearance-coordinate fiber over `S` is covered by
exact zero-agreement appearance fibers over all exact profiles `T` satisfying
`S ⊆ T ⊆ directionZeroSet u1`.  Thus exact-profile estimates can recover a coarse appearance
estimate, but only after summing over all such supersets; the combinatorial loss is now a named
interface rather than an implicit obstacle.
Follow-up zero-safe wrappers
`appearingCoordinateAgreementFiber_subset_safeExactSuperset_biUnion`,
`appearingCoordinateAgreementFiber_card_le_sum_exactAppearingBudget_safeSupersets`, and
`zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_safeSupersetSums` restrict the
sum to exact profiles of size `< a` on safe lines and package the resulting exact-to-coarse budget
consumer.

## [2026-06-27] reduce | binomial envelope for safe exact supersets

Closed the safe exact-superset sum by cardinality profile in `LineListAppearanceFiber.lean`.
`powersetCard_superset_card_le_choose_sdiff` injects fixed-size supersets `T` of a coarse profile
`S` inside `Z` into subsets of `Z \ S`, giving the cost
`choose(#Z - #S, #T - #S)`.  `sum_safeSupersets_le_sum_choose_sdiff` sums this over `#T < a`, and
`zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_chooseProfileSums` packages the
new exact-to-coarse budget transfer: an exact profile budget `M` recovers a coarse budget after
paying `sum_{r<a} choose(#Z - t, r - t) * M r`.

## [2026-06-27] reduce | concrete floor successor scanner bridge

Added `Frontier/FloorClosureSuccessorScanner.lean`, connecting the generic `UniformFrom` /
`SuccessorStep` finite-rung scanner to the concrete `CandidateListExactAt FloorBad` predicate in
`_FloorClosureContract.lean`.  A verified concrete prefix plus `CandidateListExactSuccessor` now
yields `CandidateListExactSmallestFamily`; conversely, if a verified prefix does not extend to
uniform singleton exactness, the bridge returns an adjacent rung where exactness holds at `a` and
fails at `a + 1`.

Follow-up normal forms sharpen the same successor lane:
`candidateListExactSmallestFamily_iff_base_and_successor` says uniform singleton exactness is
exactly `CandidateListExactAt 4` plus `CandidateListExactSuccessor`.
`not_candidateListExactSmallestFamily_iff_not_base_or_exists_exact_rung_next_fails` says a failed
uniform theorem is either base-rung failure or an adjacent exact-then-failing rung; once the base
is known, the latter is equivalent to uniform failure.  The generic finite-rung scanner now also
has cutoff-refined witnesses
`exists_next_failure_at_or_after_cutoff_of_verifiedPrefix_of_not_uniformFrom` and
`exists_next_failure_at_or_after_cutoff_of_verifiedOn_Icc_of_not_uniformFrom`, so a verified prefix
pushes any adjacent successor failure to the boundary or beyond.

Follow-up consumer bridge: `Frontier/FloorClosurePrefixConsumer.lean` now composes verified prefix
evidence and `CandidateListExactSuccessor` with the sharp Linnik/TZ budgeted-global-max contracts.
The new consumers are
`worstCaseIncidenceBounded_of_linnik_prefix_successor_budgetedMax`,
`deltaStar_pin_of_linnik_prefix_successor_budgetedMax`,
`worstCaseIncidenceBounded_of_tz_prefix_successor_budgetedMax`, and
`deltaStar_pin_of_tz_prefix_successor_budgetedMax`.  This keeps the remaining floor-prize inputs
exactly visible: a real successor theorem, least-prime supply, and a budgeted global maximizer.

## [2026-06-27] reduce | low exact appearance collapses to low support-ratio-heavy

Extended `LineListSupportRatioFiber.lean` with low-profile support-ratio-heavy to exact-appearance
bridges:
`zeroLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyCoordinateFiberBudgeted`
and
`uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted`.
The contrapositive wrappers
`not_zeroLowSupportRatioHeavyBudgeted_of_not_zeroLowExactAppearingBudgeted` and
`not_uniformLowSupportRatioHeavyBudgeted_of_not_uniformLowExactAppearingBudgeted` record that a
failed low exact appearance budget is already a failure of the sharper low support-ratio-heavy
coordinate-fiber budget.

Follow-up: `LineListSupportRatioFiber.lean` now exposes an all-threshold support-ratio cover
baseline with interpolation tail `|F|^(k-a)`, through
`supportRatioCoverSum_le_field_card_mul_choose_mul_field_pow_sub`,
`uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverFieldPow_n`, and
`uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_lineFiberCoverFieldPow_n`.
This removes the artificial high-threshold assumption from the cover baseline; when `a < k`, the
residual is the explicit tail rather than an implicit missing lemma.

Follow-up: `LineListAppearanceFiberMixedProfile.lean` now has a mixed low-exact/high-singleton
profile consumer.  `uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSums` charges low
exact profiles to `Mexact r` and high exact profiles to the RS singleton ceiling, while
`unsafe_or_largeZero_safe_low_mixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted` localizes
failure to either zero-direction saturation or one oversized mixed choose-profile sum.
The same file also records `*_fullMixedChooseProfileSums` variants for callers willing to pay the
mixed profile inequality for every coarse `t < a` rather than only the low coarse range.

Follow-up: `LineListAppearanceFiberMixedProfile.lean` now composes the support-ratio
`lineFiberCoverFieldPow` exact budget into both mixed-profile sockets.  The new
`uniformLineBadScalarsBudgeted_of_lineFiberCoverFieldPow_mixedChooseProfileSums` and
`uniformLineBadScalarsBudgeted_of_lineFiberCoverFieldPow_fullMixedChooseProfileSums` wrappers
instantiate the exact-profile budget as `|F| * choose(n, a-r) * |F|^(k-a)`, and their scanner
forms expose either zero-direction saturation or an oversized mixed profile sum.  The staged
`LineListSupportRatioMixedProfile.lean` sibling records the abstract version for arbitrary low
support-ratio-heavy budgets through
`uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileSums` and its full-profile
variant.

Follow-up: the mixed-profile arithmetic residual is now named by
`ZeroLowMixedChooseProfileSumsFit` and
`UniformLargeZeroSafeLowMixedChooseProfileSumsFit`.  Its exact failure form is one oversized mixed
sum, and `lowMixedChooseProfileSumsFit_term_le` exposes single-summand necessary conditions.  In
particular, both the same-profile low exact term and every high singleton binomial term must fit
under `Mcoarse t`; one over-budget high binomial contribution refutes the mixed route.  The
cardinal-profile wrappers reduce this arithmetic to inequalities in `a <= z <= n`.

## [2026-06-27] reduce | promote finite-rung floor barrier

Renamed the finite-rung floor-localization guardrail from the scratch file
`_FloorFiniteRungUniformityBarrier.lean` to the landed Frontier module
`FloorFiniteRungUniformityBarrier.lean`.  The theorem surface now also includes
`verifiedOn_Icc_iff_verifiedPrefix`, so callers can switch between interval-finset evidence and
prefix evidence without reproving the bridge.

`two_rung_floor_evidence_not_uniform` still records that the checked `a = 4, 5` rungs alone do
not imply `UniformFrom 4 R`, and `two_rung_floor_interval_evidence_not_uniform` states the same
guardrail for `VerifiedOn (Finset.Icc 4 5)`.  `SuccessorStep`,
`not_uniformFrom_iff_exists_failure`, and `not_successorStep_iff_exists_next_failure` expose the
missing all-rungs propagation as a scanner target: either prove the successor step or find a
checked rung where propagation fails.

Follow-up: the finite-rung barrier now has prefix-consumer scanners.  The wrappers
`not_successorStep_of_verifiedPrefix_of_not_uniformFrom`,
`not_successorStep_of_verifiedOn_Icc_of_not_uniformFrom`,
`exists_next_failure_of_verifiedPrefix_of_not_uniformFrom`, and
`exists_next_failure_of_verifiedOn_Icc_of_not_uniformFrom` say that once the checked prefix is
accepted, any remaining failure of all-rungs uniformity must produce an adjacent rung where
`R(a)` holds but `R(a+1)` fails.

## [2026-06-27] reduce | exact floor depth scale gates

Promoted `_FloorLevelDepthPrimeScaleGate.lean` to the landed Frontier module
`FloorLevelDepthPrimeScaleGate.lean`, narrowed its import from `Mathlib.Tactic` to
`Mathlib.Tactic.Linarith`, and sharpened the arithmetic surface.  The exact gates
`dyadic_level_power_le_prize_iff_mul_le` and `dyadic_prize_lt_level_power_iff_mul_lt` state that
level/exponent supply fits or overshoots the base quartic prize window exactly according to the
product comparison `k * e <= 4a`.  The cubic specializations
`cubic_deeper_level_le_prize_iff_depth` and
`prize_lt_cubic_deeper_level_iff_depth_too_large` isolate the depth condition as precisely
`3d <= a` versus `a < 3d`.  The helper `level_witness_le_prize_of_mul_le` packages the reusable
witness transfer below prize scale, and fifth-power Linnik scale remains ruled out at every
nontrivial deeper level.

Follow-up witness scanners
`mul_lt_of_prize_lt_level_witness`, `not_prize_lt_level_witness_of_mul_le`,
`depth_too_large_of_prize_lt_cubic_level_witness`, and
`not_prize_lt_cubic_level_witness_of_depth` make the gate refutable at the supplied-prime level:
if a prime witness lies under the level/exponent supply but still above the base prize scale, the
exponent product has already failed; in the cubic case the extra depth must satisfy `a < 3d`.
