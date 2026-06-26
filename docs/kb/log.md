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
