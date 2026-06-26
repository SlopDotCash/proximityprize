# Issue #464: line-list budget gate for ratio-census attacks

Date: 2026-06-26.

Status: **scanner-interface progress**, not a delta-star proof.

## Thesis

The ratio-census and per-codeword heavy-scalar files already prove the local part of the affine-line
story: a fixed codeword can be close to only `floor(n/a)` scalars on a line when the direction is
nonzero coordinatewise.  The support-aware follow-up removes that artificial hypothesis: if
`z = #{i : u1 i = 0}` and `z < a`, the per-codeword budget becomes
`support(u1)/(a-z)`.  The remaining positive obligation is still not another ratio identity.  It is
a line-list-size theorem: how many codewords appear anywhere along the affine line.

This pass names that boundary directly in:

```text
ArkLib/Data/CodingTheory/ProximityGap/LineListReduction.lean
```

## New API

The local sets are now first-class declarations:

```lean
directionZeroSet
directionSupportSet
directionZeroAgreementSet
lineBadScalars
lineAppearingCodewords
LineListBudgeted
SupportEligibleLineDirection
UniformSupportLineListBudgeted
SupportAdjustedLineBadScalarsBudgeted
```

The positive consumer is:

```lean
lineBadScalars_card_le_of_lineListBudgeted
lineBadScalars_card_le_of_lineListBudgeted_support_div_sub_zero
```

It states the exact budget law:

```text
lineAppearingCodewords.card <= L
=> lineBadScalars.card <= L * floor(n/a)
```

The support-aware version says:

```text
z = directionZeroSet(u1).card
z < a
lineAppearingCodewords.card <= L
=> lineBadScalars.card <= L * (directionSupportSet(u1).card / (a-z)).
```

It is backed by the per-codeword local bounds:

```lean
directionZeroAgreementSet_subset_agreeSet_line
heavyScalarSet_eq_univ_of_directionZeroAgreement_ge
heavyScalarSet_card_eq_field_card_of_directionZeroAgreement_ge
lineBadScalars_eq_univ_of_codeword_directionZeroAgreement_ge
lineBadScalars_card_eq_field_card_of_codeword_directionZeroAgreement_ge
directionZeroAgreement_lt_of_lineBadScalars_card_lt_field_card
agreeSet_line_card_le_zero_add_movingFiber
codeword_heavy_scalar_card_le_support_div_sub_zero
lineBadScalars_card_le_lineAppearingCodewords_card_mul_support_div_sub_zero
```

The zero-direction branch is sharp: if the fixed codeword already agrees with the offset on at
least `a` zero-direction coordinates, then every scalar is heavy for that codeword.  If that
codeword is in `rsCode dom k`, then the whole line bad-scalar set is `univ`.  Conversely, any line
whose bad-scalar set is smaller than the whole field rules out this saturation branch for every
appearing codeword.  The support-adjusted budget is therefore only useful after excluding that
branch, or after proving it cannot occur for the deployed line/codeword family.

The old theorem `badScalar_card_le_lineList_mul` already contained this argument internally.  The
new forms are meant for downstream scanners and proof attempts that want to supply a candidate
line-list bound without unfolding the bipartite cover proof or assuming a nowhere-zero direction.

## Refutation Surface

The scanner-facing contrapositives are:

```lean
not_lineListBudgeted_of_lineBadScalars_card_gt
lineAppearingCodewords_card_gt_of_lineBadScalars_card_gt
not_lineListBudgeted_of_lineBadScalars_card_gt_support_div_sub_zero
lineAppearingCodewords_card_gt_of_lineBadScalars_card_gt_support_div_sub_zero
not_uniformSupportLineListBudgeted_iff_exists_eligible_lineAppearing_gt
not_supportAdjustedLineBadScalarsBudgeted_iff_exists_eligible_lineBadScalars_gt
not_uniformSupportLineListBudgeted_of_exists_eligible_lineBadScalars_gt
```

So any over-budget line:

```text
L * floor(n/a) < lineBadScalars.card
```

does not falsify the per-codeword ratio-census layer.  It proves instead that the affine line has
more than `L` appearing codewords.  The obstruction is an oversized line list.

## Consequence

This is a useful audit split.  Ratio-census identities, Markov-on-support bounds, and
heavy-scalar lemmas can bound each codeword's scalar contribution.  They cannot by themselves
control how many codewords appear along the whole line.

The remaining non-tautological route is therefore:

```text
prove a subtrivial bound on lineAppearingCodewords.card
```

for the deployed affine lines, or produce a scanner witness showing that any proposed bound `L` is
too small.  That is exactly the affine-line list-decoding core, not a floor/localization shortcut.

## Literature/PDF Inventory Note

The local scan covered 327 PDFs under `/Users/shawwalters/papers/arklib` and 10 PDFs under
`docs/references/proximity-gap-paley-spectrum`, 337 total across those two corpora.  The relevant
Littlewood-Offord, character-sum, and list-decoding notes keep returning to the same split:
anti-concentration controls one line/codeword interaction, while the prize-scale closure still
needs a production line-list bound.  No paper in this pass supplied that missing bound as a theorem
ready to plug into `LineListBudgeted`.

Filename hits around the line-list/list-decoding lane included:

```text
BCIKS20-proximity-gaps.pdf
BermanShanyTamo-ExplicitSubcodesRSCapacity.pdf
LiShagrithaya-ListRecoveryLinearCodes.pdf
LiShagrithaya-NearOptimalListRecoveryLinearCodeFamilies-2502.13877.pdf
LeviMosheiffShagrithaya-RandomRSRandomLinearLocallyEquivalent-2406.02238.pdf
arxiv-2603.03841-AdvancesListDecodingPolynomialCodes.pdf
arxiv-2605.07595-SyndromeSpaceProximityGapsRandomLinearCodes.pdf
eprint-2026-782-HKK-FailureProximityGaps.pdf
```

These are still valuable references, but this pass did not find a statement with the exact
production shape:

```text
LineListBudgeted dom k a u0 u1 L
```

for the deployed affine lines and prize-scale thresholds.

## Continuation: support-aware directions

The first line-list split assumed the direction `u₁` was nonzero on every coordinate.  That is a
clean special case, but it is stronger than the affine-line geometry needs.  The support-aware
update adds:

```lean
directionZeroSet
directionSupportSet
agreeSet_line_card_le_zero_add_movingFiber
codeword_heavy_scalar_card_le_support_div_sub_zero
lineBadScalars_card_le_lineAppearingCodewords_card_mul_support_div_sub_zero
lineBadScalars_card_le_of_lineListBudgeted_support_div_sub_zero
not_lineListBudgeted_of_lineBadScalars_card_gt_support_div_sub_zero
lineAppearingCodewords_card_gt_of_lineBadScalars_card_gt_support_div_sub_zero
```

If `z = #directionZeroSet u₁` and `z < a`, a fixed codeword is heavy for at most

```text
#directionSupportSet(u₁) / (a - z)
```

scalars.  The line-list gate therefore works for directions with zeros, as long as the zero support
does not already meet the agreement threshold.  The residual is still the same line-list-size
theorem; the per-codeword layer is no longer blocked by an artificial nowhere-zero assumption.

The excluded case is now explicit rather than hidden: if the zero-direction set already has
`a <= z`, then the line can be heavy for reasons unrelated to moving scalar fibers.  That branch has
to be handled by the near-code/zero-direction machinery or by a separate pair-joint argument.  The
support-aware lemma only closes the small-zero-set side of the split.

## Continuation: uniform eligible-line budget

The route is now family-facing.  A line-list proof for one affine line is only a local certificate;
the production target must quantify over every eligible affine line:

```lean
UniformSupportLineListBudgeted dom k a L
```

This says that every `u0,u1` with `#directionZeroSet(u1) < a` has at most `L` appearing codewords.
The consumer is:

```lean
supportAdjustedLineBadScalarsBudgeted_of_uniformSupportLineListBudgeted
```

and it gives the support-adjusted bad-scalar budget on every eligible line:

```text
lineBadScalars.card <=
  L * floor(#directionSupportSet(u1) / (a - #directionZeroSet(u1))).
```

The new failure witnesses are exact:

```lean
not_uniformSupportLineListBudgeted_iff_exists_eligible_lineAppearing_gt
not_supportAdjustedLineBadScalarsBudgeted_iff_exists_eligible_lineBadScalars_gt
not_uniformSupportLineListBudgeted_of_exists_eligible_lineBadScalars_gt
```

So a scanner can now refute a proposed uniform line-list theorem by one eligible line with too many
appearing codewords, or by one eligible line whose bad-scalar count beats the support-adjusted
budget.  This is still not a proof of the #464 floor; it is the exact all-eligible-line production
obligation that would have to be compared to the canonical worst-case incidence core.

## Continuation: zero-direction saturation

The complement of the support-aware condition is sharp.  The new zero-direction socket adds:

```lean
directionZeroAgreementSet
directionZeroAgreementSet_subset_agreeSet_line
heavyScalarSet_eq_univ_of_directionZeroAgreement_ge
lineBadScalars_eq_univ_of_codeword_directionZeroAgreement_ge
directionZeroAgreement_lt_of_lineBadScalars_card_lt_field_card
ZeroDirectionSafeLine
UniformZeroDirectionSafe
UniformLineBadScalarsBudgeted
SupportAdjustedBudgetFits
LargeZeroSafeLineBadScalarsBudgeted
not_zeroDirectionSafeLine_iff_exists_codeword_zeroAgreement_ge
lineBadScalars_eq_univ_of_not_zeroDirectionSafeLine
lineBadScalars_card_eq_field_card_of_not_zeroDirectionSafeLine
zeroDirectionSafeLine_of_lineBadScalars_budget_lt_field
uniformZeroDirectionSafe_of_uniformLineBadScalarsBudgeted_lt_field
not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
not_uniformLineBadScalarsBudgeted_of_not_uniformZeroDirectionSafe_lt_field
not_uniformLineBadScalarsBudgeted_iff_exists_lineBadScalars_gt
not_largeZeroSafeLineBadScalarsBudgeted_iff_exists_largeZero_safe_lineBadScalars_gt
not_uniformLineBadScalarsBudgeted_iff_eligible_or_unsafe_or_largeZero_safe
zeroAgreementStratum
puncturedZeroStratifiedLineWeight
PuncturedZeroStratifiedLineBudgeted
UniformPuncturedZeroStratifiedLineBudgeted
ZeroAgreementStrataCardBudgeted
ZeroAgreementStrataBudgetFits
UniformLargeZeroSafeZeroAgreementStrataCardBudgeted
UniformLargeZeroSafeZeroAgreementStrataBudgetFits
lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
puncturedZeroStratifiedLineWeight_le_of_zeroAgreementStrataCardBudgeted
puncturedZeroStratifiedLineBudgeted_of_zeroAgreementStrataCardBudgeted
uniformPuncturedZeroStratifiedLineBudgeted_of_uniformZeroAgreementStrataCardBudgeted
lineBadScalars_card_le_of_puncturedZeroStratifiedLineBudgeted
largeZeroSafeLineBadScalarsBudgeted_of_uniformPuncturedZeroStratifiedLineBudgeted
not_puncturedZeroStratifiedLineBudgeted_iff_weight_gt
not_uniformPuncturedZeroStratifiedLineBudgeted_iff_exists_largeZero_safe_weight_gt
puncturedZeroStratifiedLineWeight_gt_of_lineBadScalars_card_gt
not_uniformPuncturedZeroStratifiedLineBudgeted_of_not_largeZeroSafeLineBadScalarsBudgeted
not_zeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
not_zeroAgreementStrataBudgetFits_iff_sum_gt
not_uniformLargeZeroSafeZeroAgreementStrataBudgetFits_iff_exists_sum_gt
not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_of_not_uniformPunctured
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_puncturedZeroStratified
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_zeroAgreementStrata
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
```

If a codeword already agrees with the offset `u0` on at least `a` coordinates where `u1 = 0`, then
those coordinates agree for every scalar `gamma`.  The fixed-codeword heavy-scalar set is all of
`F`, and if that codeword is in `rsCode dom k`, then:

```text
lineBadScalars dom k a u0 u1 = univ.
```

So the excluded branch is not an artifact of the proof.  It can saturate the scalar field.  Any
nontrivial bad-scalar upper bound for a line must therefore prove:

```text
for every codeword c in rsCode dom k,
#directionZeroAgreementSet(c,u0,u1) < a.
```

This turns the zero-direction branch into a clean near-code residual.  It does not help prove the
floor directly; it prevents a false proof from smuggling a large zero-coordinate agreement set
through the support-adjusted denominator.

The newest socket packages that residual as a production-side necessity.  Define:

```lean
ZeroDirectionSafeLine dom k a u0 u1
UniformZeroDirectionSafe dom k a
UniformLineBadScalarsBudgeted dom k a B
```

If `B < |F|`, then:

```lean
uniformZeroDirectionSafe_of_uniformLineBadScalarsBudgeted_lt_field
```

says any uniform bad-scalar budget `B` forces zero-direction safety for every line.  Conversely:

```lean
not_uniformLineBadScalarsBudgeted_of_not_uniformZeroDirectionSafe_lt_field
```

says one unsafe zero-direction line refutes every uniform budget below field size.  In the prize
regime this is the right polarity: the desired budget is near `n`, while the field has size near
`n * 2^128`, so zero-direction saturation is an immediate blocker for any floor proof.

## Continuation: support/large-zero trichotomy

The uniform line-list route now has a complete named-set decomposition:

```lean
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
```

It proves `UniformLineBadScalarsBudgeted dom k a B` from four explicit inputs:

```text
1. UniformSupportLineListBudgeted dom k a L
2. SupportAdjustedBudgetFits a L B
3. UniformZeroDirectionSafe dom k a
4. LargeZeroSafeLineBadScalarsBudgeted dom k a B
```

The first input is the production line-list theorem on support-eligible directions.  The second is
only arithmetic: the direction-dependent support-adjusted bound must fit under the target `B`.  The
third rules out zero-direction saturation.  The fourth is now the exact remaining branch:

```text
#directionZeroSet(u1) >= a,
zero-direction safe,
but still possibly many bad scalars.
```

Its falsifier is:

```lean
not_largeZeroSafeLineBadScalarsBudgeted_iff_exists_largeZero_safe_lineBadScalars_gt
```

So the line-list lane is no longer a single vague "bound the affine-line list" task.  It is a
four-part production contract, and the genuinely new piece is the large-zero safe residual.  That
residual is not solved here; it is isolated as the next place where near-code geometry or a
pair-joint argument has to do real work.

The latest failure theorem makes the negative side exact when the target budget is below field size:

```lean
not_uniformLineBadScalarsBudgeted_iff_eligible_or_unsafe_or_largeZero_safe
```

So any failed production line-list budget must now surface as one of:

```text
1. support-eligible direction over budget,
2. zero-direction saturation,
3. large-zero, zero-safe direction over budget.
```

This is the useful scanner form.  It separates the arithmetic support-fit problem, the near-code
saturation obstruction, and the residual large-zero geometry instead of letting them blur into one
"line-list failed" message.

## Continuation: punctured zero-stratified large-zero socket

The large-zero safe residual now has a positive consumer instead of only a name.  The new
codeword-level lemmas are:

```lean
agreeSet_line_card_le_zeroAgreement_add_movingFiber
codeword_heavy_scalar_card_le_support_div_sub_zeroAgreement
```

They replace the old denominator `a - #directionZeroSet(u1)` with

```text
a - #directionZeroAgreementSet(c,u0,u1)
```

for each codeword `c`.  This is the right correction in the large-zero branch: even when
`#directionZeroSet(u1) >= a`, a zero-safe line still gives
`#directionZeroAgreementSet(c,u0,u1) < a` for every codeword in the RS code.

The line-level declarations are:

```lean
zeroAgreementStratum
puncturedZeroStratifiedLineWeight
PuncturedZeroStratifiedLineBudgeted
UniformPuncturedZeroStratifiedLineBudgeted
ZeroAgreementStrataCardBudgeted
ZeroAgreementStrataBudgetFits
UniformLargeZeroSafeZeroAgreementStrataCardBudgeted
UniformLargeZeroSafeZeroAgreementStrataBudgetFits
lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
puncturedZeroStratifiedLineWeight_le_of_zeroAgreementStrataCardBudgeted
puncturedZeroStratifiedLineBudgeted_of_zeroAgreementStrataCardBudgeted
uniformPuncturedZeroStratifiedLineBudgeted_of_uniformZeroAgreementStrataCardBudgeted
lineBadScalars_card_le_of_puncturedZeroStratifiedLineBudgeted
largeZeroSafeLineBadScalarsBudgeted_of_uniformPuncturedZeroStratifiedLineBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_puncturedZeroStratified
not_puncturedZeroStratifiedLineBudgeted_iff_weight_gt
not_uniformPuncturedZeroStratifiedLineBudgeted_iff_exists_largeZero_safe_weight_gt
puncturedZeroStratifiedLineWeight_gt_of_lineBadScalars_card_gt
not_uniformPuncturedZeroStratifiedLineBudgeted_of_not_largeZeroSafeLineBadScalarsBudgeted
not_zeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
not_zeroAgreementStrataBudgetFits_iff_sum_gt
not_uniformLargeZeroSafeZeroAgreementStrataBudgetFits_iff_exists_sum_gt
not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_of_not_uniformPunctured
exists_eligible_or_unsafe_or_largeZero_stratum_of_not_uniformLineBadScalarsBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_zeroAgreementStrata
exists_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
```

The main inequality is:

```text
lineBadScalars.card
  <= sum over appearing codewords c
       #directionSupportSet(u1) /
         (a - #directionZeroAgreementSet(c,u0,u1)).
```

The exact regrouping theorem rewrites that weight as:

```text
sum_{t < a}
  #zeroAgreementStratum(dom,k,a,u0,u1,t) *
    #directionSupportSet(u1)/(a-t).
```

A proof of `UniformPuncturedZeroStratifiedLineBudgeted` now plugs directly into the production
wrapper together with the support-eligible line-list theorem and the arithmetic support-fit check.
Conversely, any large-zero safe raw bad-scalar counterexample also overbudgets the punctured weight,
so scanners can target the stronger weighted certificate directly.

The weight can now be attacked through explicit zero-agreement strata.  A proposed function `N t`
with:

```lean
ZeroAgreementStrataCardBudgeted dom k a u0 u1 N
ZeroAgreementStrataBudgetFits a B u1 N
```

gives `PuncturedZeroStratifiedLineBudgeted`; uniformly, the corresponding large-zero-safe stratum
cardinality and arithmetic-fit hypotheses imply `UniformPuncturedZeroStratifiedLineBudgeted`.  This
turns the next proof obligation into a concrete family of `t < a` near-code packing bounds.

The field is still open here: the hard part is bounding this weighted appearing-codeword list, not
the local per-codeword scalar count.

The weighted-list bound now has an explicit `N(t)` envelope interface:

```lean
ZeroAgreementStrataCardBudgeted
ZeroAgreementStrataBudgetFits
UniformLargeZeroSafeZeroAgreementStrataCardBudgeted
UniformLargeZeroSafeZeroAgreementStrataBudgetFits
puncturedZeroStratifiedLineWeight_le_of_zeroAgreementStrataCardBudgeted
uniformPuncturedZeroStratifiedLineBudgeted_of_uniformZeroAgreementStrataCardBudgeted
```

This factors the next theorem into two pieces: prove
`#zeroAgreementStratum(t) <= N(t)` on every large-zero safe line, then verify
`sum_{t<a} N(t) * support(u1)/(a-t) <= B`.

The corresponding negative forms keep this split honest:

```lean
not_zeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
not_zeroAgreementStrataBudgetFits_iff_sum_gt
not_uniformLargeZeroSafeZeroAgreementStrataBudgetFits_iff_exists_sum_gt
not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_of_not_uniformPunctured
exists_eligible_or_unsafe_or_largeZero_stratum_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
```

Thus a failed zero-strata proof reports either an overfull `t`-stratum or an arithmetic envelope
whose weighted sum already exceeds `B`.  With the arithmetic fit fixed, any punctured-budget failure
forces an overfull stratum.

The newest scanner composition moves this up to the full line-list route.  With the large-zero
`N(t)` arithmetic fit fixed, a failed uniform bad-scalar budget has to be eligible-line overbudget,
zero-direction saturation, or a concrete overfull large-zero stratum.  If the support-eligible
line-list theorem, support arithmetic, and zero-direction safety are also fixed, only the overfull
large-zero stratum can remain.

The latest refinement opens that stratum through a raw coordinate-fiber API:

```lean
coordinateAgreementFiber
ZeroCoordinateAgreementFiberBudgeted
ZeroCoordinateAgreementFiberBudgetFits
coordinateAgreementFiber_card_le_one_of_k_le
coordinateAgreementFiber_card_le_field_pow_sub_card
zeroCoordinateAgreementFiberBudgeted_field_pow_sub_card
uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_field_pow_sub_card
uniformFieldPowCoordinateAgreementFiberBudgetFits_term_le
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_term_gt
fieldPowCoordinateAgreementFiberBudgetFits_choosePow_le_of_support_ge_sub
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_choosePow_gt
uniformFieldPowCoordinateAgreementFiberBudgetFits_zeroTerm_le
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_zeroTerm_gt
uniformFieldPowCoordinateAgreementFiberBudgetFits_cardPow_le_of_exists_support_ge
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_support_ge
exists_direction_zero_card_eq_support_card_eq
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_zero_count_choosePow_gt
exists_largeZero_direction_support_ge_of_two_mul_le
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_two_mul_le
zeroAgreementStratum_card_le_choose_of_k_le_t
unsafe_or_largeZero_safe_low_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_coordinateAgreementFibers
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_fieldPowCoordinateFibers
unsafe_of_not_uniformLineBadScalarsBudgeted_with_fieldPowCoordinateFibers
```

`coordinateAgreementFiber` is the raw RS fiber of all codewords agreeing with `u0` on a fixed
zero-coordinate subset `S`; summing over all `t`-subsets covers the exact `t`-stratum.  It already
has the endpoint theorem that a fiber over `#S >= k` has size at most one, and this now lifts to
the stratum bound `#zeroAgreementStratum(t) <= choose(#zeroSet(u1), t)` for `k <= t`.  The raw
affine interpolation count is also formalized as
`#coordinateAgreementFiber(S) <= |F|^(k - #S)` with only the standard Lean axioms.  Thus the
remaining `N(t)` problem is no longer the basic fiber count; it is whether the induced low-range
weighted binomial arithmetic fits, or whether a support-aware refinement is needed.  If the
field-power weighted fit does hold, any remaining uniform-budget failure is forced into
zero-direction saturation.  The same arithmetic fit must already pass every individual summand
test; under support at least `a - t`, the `t` term alone forces
`choose(#zeroSet(u1), t) * |F|^(k-t) <= B`.  In particular, the `t = 0` test forces
`|F|^k * support(u1) / a <= B` on every large-zero direction; with support at least `a`, this
already forces `|F|^k <= B`.  Since such a direction exists whenever `2a <= n`, the raw field-power
fit is formally impossible in that regime for any `B < |F|^k`.  The parameterized obstruction is
sharper: a direction with exactly `z` zeros and support `n-z` exists for every `z <= n`, so any
single term with `a <= z`, `t < a`, `a - t <= n-z`, and
`B < choose(z,t) * |F|^(k-t)` refutes the raw field-power fit.  If a weaker proposed envelope
fails, the new scanner returns an explicit low stratum or low overfull coordinate fiber.
