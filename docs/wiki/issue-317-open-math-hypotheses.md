# Issue #317/#327/#313: Open-Math Hypothesis Ledger (2026-06-10)

> **Historical snapshot (2026-06-10).** This ledger records the state and plans of that date; it
> is not an authority for current completion status. Module paths it cites (for example
> `Soundness/Proposition421.lean`) were later consolidated, and the residual classes it lists as
> remaining have since been retired or replaced by direct theorems. For the current module map
> see [`issue-317-binius-residuals.md`](issue-317-binius-residuals.md) (Current navigation) and
> for open residuals see [`residual-census.md`](residual-census.md).

> Companion ledger: a parallel goal-session produced
> [`docs/kb/audits/issue-317-327-binius-residual-hypothesis-ledger-2026-06-10.md`](../kb/audits/issue-317-327-binius-residual-hypothesis-ledger-2026-06-10.md)
> (full 9-residual census + H-K/H-A series, committed `a3ea3f485`). The two ledgers were
> written independently and agree on the headline (no open mathematics remains; the DG25
> wall is already down in-tree). This file adds the exact in-tree DG25→Cor 3.7 declaration
> chain for Case 2, the refuted-A4 anti-LARP record, and the K1 brick decomposition being
> proven by workflow `prop421case1-discharge`.

Scope: the remaining *mathematical* (non-wiring) surface of the Binius Binary Basefold
soundness closeout, after the 2026-06-10 fleet wave discharged
`FoldMatrixDetNeZeroResidual`, `PreTensorCombineMultilinearResidual`,
`FoldPreTensorCombineAffineSplitResidual`, `FinalSumcheckStepLogicCompleteResidual`,
`ExtractMLPCorrectnessResidual`, and `FoldPreservesBBFCodeMembershipResidual`.

Remaining named classes: `Prop421Case1FiberwiseCloseResidual`,
`Prop421Case2FiberwiseFarResidual` (`Soundness/Proposition421.lean`),
`Prop4212Case1Residual`, `Prop4212Case2Residual`, and the joint-proximity bridge
(`Soundness/Incremental.lean`, active separate lane).

Method per the session goal: for each hypothesis, first the constraints, the prior-art
check ("has someone already done this / am I LARPing"), and what is genuinely novel;
then the hypothesis; then the prove-out disposition.

## Source map (verified in-tree, all 0-sorry unless stated)

- DP24 = Diamond–Posen 2024/504. Prop 4.21 p.40: Case 1 = per-fiber Schwartz–Zippel +
  union bound (eq. 39); Case 2 = Lemma 4.22 far-lift + Theorem 2.4.
- DP24 Theorem 2.4 = DG25 Cor. 1 (tensor proximity gap within UDR, error ϑ·n/|L|).
- In-tree chain for Theorem 2.4: BCIKS20 UD base case
  (`RS_correlatedAgreement_affineLines_uniqueDecodingRegime`, consumed by proven
  `ahiv17_*_uniqueDecodingRegime` in `ProximityGap/AHIV22.lean`) → DG25 Thm 3.1
  (`affine_gaps_lifted_to_interleaved_codes`) → AER24 Thm 3.6
  (`interleaved_affine_gaps_imply_tensor_gaps`) → Cor 3.7
  (`reedSolomon_multilinearCorrelatedAgreement_Nat`, `DG25/ReedSolomon.lean`).
- `BBF_Code` is definitionally `ReedSolomon.code` (`BinaryBasefold/Code.lean:64`).
- Fold-matrix nonsingularity: `foldMatrix_det_ne_zero` (`FoldDetDischarge.lean`).
- Single-point bridge: `single_point_localized_fold_matrix_form_eq_iterated_fold`
  (`Prelude.lean`, working tree), where the matrix form is
  `⟨challengeTensorProduct(r), foldMatrix_y *ᵥ fiberEvaluations⟩`.
- SZ leaf: `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le`
  (`Data/Probability/Instances.lean`).

## Known-math hypotheses (K1–K5)

### K1 — Case 1 closes by tensor-polynomial Schwartz–Zippel
*Constraints:* the residual's event is `¬(Δ_perFiber ⊆ Δ(fold f, fold f̄))` over uniform
`r ∈ L^steps`; bound `steps·|S_next|/|L|` in ENNReal. *Prior art:* the math is DP24's own
proof — no novelty claimed in content; the formal novelty is the missing machinery: an
`MvPolynomial` mirror of `challengeTensorProduct` with cube-indicator and eval lemmas, a
`Pr_`-level finset union bound, and the matrix-nonsingularity consumption. Nobody has
formalized DP24 Prop 4.21 before (in any proof assistant, to our knowledge — the only
Binius formalization effort is this repo). *Hypothesis:* the residual is provable in-tree
with exactly: tensor polynomial `S(a) = Σ_idx C(a idx)·T_idx(X)` (recursion mirroring
`challengeTensorProduct_succ_get`), eval bridge, snoc-indexed cube indicator
`eval(bits(j))(S(a)) = a j`, `totalDegree ≤ steps`, `a := M_y *ᵥ Δv ≠ 0` from
`det ≠ 0` + `Δv ≠ 0`, per-fiber SZ, finset union bound. *Disposition:* PROVE NOW
(workflow `prop421case1`).

### K2 — Case 2 is wiring, not math
*Constraints:* statement bounds `Pr[UDRClose(fold f r)] ≤ steps·|S_next|/|L|` under
fiberwise-far. *Prior-art check:* I verified the full DG25 chain is already proven
in-tree (see source map) — an earlier session note calling this "the genuinely deep
external math" is now WRONG; claiming new math here would be LARPing. *Hypothesis:* Case
2 closes with zero new mathematics: Lemma 4.22 far-lift (PreTensor lane, in flight) +
Cor 3.7 instantiated at `BBF_Code = ReedSolomon.code` + the proven
`iterated_fold = multilinearCombine ∘ preTensorCombine` bridge + a probability-form
contrapositive bridge. *Disposition:* posted to #317; assemble after the PreTensor lane
lands (avoid file collision with the active agent).

### K3 — One SZ engine serves both Case-1 residuals
*Constraints:* `Prop4212Case1Residual` (Incremental.lean) is the incremental sibling of
Prop 4.21 Case 1; the fleet already diagnosed its old surface degenerate and built
`fiberwiseDisagreementSetPerFiber`. *Novelty:* DRY observation, not math: both reduce to
"nonzero tensor-affine combination of an invertible-matrix image vanishes w.p. ≤
steps/|L| per point". *Hypothesis:* the K1 brick file, kept `Binius`-generic (statement
over `a : Fin (2^n) → L` only), discharges the per-point leaf of BOTH residuals.
*Disposition:* design K1 bricks parametrically; offer to the Incremental lane via issue
comment.

### K4 — Legacy degenerate disagreement set migrates monotonically
*Constraints:* 44 use sites of the coarse `fiberwiseDisagreementSet`; the honest set is a
subset (`fiberwiseDisagreementSetPerFiber_subset_legacy_of_ne_zero`). *Hypothesis:* every
remaining consumer either (a) only needs the subset direction, or (b) is a bad-event
definition where shrinking the set weakens nothing downstream. *Prior art:* migration
already started by the fleet (bad events migrated). *Disposition:* verify during #313
closeout sweep; no new math expected.
*Status (resolved):* after the ArkLib consolidation the canonical `fiberwiseDisagreementSet`
is the per-fiber set, and `fiberwiseDisagreementSetPerFiber` is definitionally equal to it. The
coarse all-or-empty surface is retained only as
`Compatibility.globalDisagreementDestinations` (`Soundness/FoldDistance.lean`; no locality claim),
and Compliance `fold_error_containment_all` now proves true per-fiber locality. The K4 migration
hypothesis is therefore resolved.

### K5 — #327 relation-out completes from the landed final-codeword bridges
*Constraints:* the issue-owner lane landed `getMidCodewords_last_apply_eq_eval`,
`finalSumcheckStep_final_codeword_eq_eval`, `getFoldingChallenges_append_finalBlock`.
*Hypothesis:* the remaining final relation-out conjunct (final committed block folded
through the last ϑ challenges equals `stmt.final_constant`) follows by composing the
challenge-split brick with the constancy corollary — no convention change needed.
*Disposition:* owner lane active; do not duplicate. Verify-only.

## Advanced hypotheses (A1–A5)

### A1 — A single "invertible tensor-fold system" abstraction
*Constraints/novelty:* Case 1, Prop 4.21.2 Case 1, the Lemma 4.9 bridges, and the query
phase consistency checks all instantiate one pattern: value = ⟨tensor(r), M·v⟩ with M
invertible per evaluation point. Nobody (in the paper or the tree) states this once;
DP24 re-derives it three times. *Hypothesis:* a structure
`InvertibleTensorFoldSystem (n : ℕ) (M : point → Matrix ...)` with one SZ lemma and one
indicator lemma subsumes all per-point probabilistic leaves in the Binius soundness
layer. *Why not done:* the per-file APIs grew bottom-up under issue pressure. *Risk:*
abstraction tax in dependent-type plumbing may exceed the savings. *Disposition:*
prototype only if K1 lands cleanly and shows shared shape with Prop4212Case1.

### A2 — Multiplicity-aware per-fiber bound (REJECTED for closeout)
*Hypothesis sketch:* if only `k < steps` refinement levels of the fiber disagree, the
per-fiber vanishing probability drops to `k/|L|` (the tensor polynomial lives in a
`k`-variable subring). *Am I LARPing check:* plausibly true and plausibly novel (DP24
doesn't need it), but it changes the public bound and benefits nothing downstream —
the union bound is already dominated by `|S_next|`. *Disposition:* documented, not
pursued.

### A3 — Case 2 beyond unique decoding (Johnson-regime BBF soundness)
*Constraints:* DP24 stays within UDR; DG25/BCIKS20 list-decoding-regime gaps for RS are
only partially in-tree (`ahiv17` row-span `d/q` specialization still residual). *Genuine
novelty:* a Johnson-radius Binary Basefold soundness theorem would be a real extension of
DP24 (would sharpen the protocol's query complexity). *Why nobody has done it:* DP24's
extractor needs unique decoding for witness extraction; list-decoding breaks extractor
uniqueness — this is the same obstruction tracked across #232's MCA program.
*Hypothesis:* rbr soundness of BBF holds at Johnson radius with the error replaced by
the BCIKS20 list-regime bound, PROVIDED a canonical-representative extractor exists.
*Disposition:* research-track; out of #317 closeout scope (would be a new issue).

### A4 — Tighter false-witness bound ε in Cor 3.7 (REFUTED — anti-LARP record)
*Hypothesis sketch:* replace `ε = n` by `ε = e+1` in the tensor gap. *Refutation:* DG25
Example 4.1 shows `ε = n` is TIGHT for RS (Ben+23 Thm 4.1 sharpness); the in-tree
docstring records this. Kept as a worked example of checking before claiming novelty.

### A5 — Char-2 constructive fold inverse
*Constraints:* over the char-2 tower, `det(foldMatrix) = (basis_x 0)^{2^steps · …}` up to
sign — a single basis element's power; the matrix inverse has closed form via the
inverse additive NTT butterfly (DP24 Remark 4.10). *Novelty:* an explicit
`foldMatrixInv` would make the Berlekamp–Welch extractor in `Relations.lean`
computational (decidable extraction, no `Classical.choice` in the extractor path) —
neither the paper nor the tree does this. *Why not done:* nobody needed computability.
*Disposition:* nice-to-have; only if #313 closeout demands extractor executability
(it does not today).

## Unification/simplification observations

- The `PreTensor*` file suite + `DG25/MainResults` both define disagreement-column sets
  (`disagreementSet`, `R_star_star` columns); after #317 closes, one of the two should
  be re-expressed through `Code.disagreementCols` (`Basic/Distance.lean`) — tracked for
  the #313 sweep.
- `fiberEvaluationMapping` (legacy, `Prelude.lean`) and `fiberEvaluations` (new API)
  coexist; the new-API bridge lemma `fiberEvaluations_apply_eq_qMap_total_fiber` makes
  the legacy one removable.
- The SZ leaf family (`prob_schwartz_zippel_*`, `schwartz_zippel_of_fintype`,
  `schwartz_zippel_counting`) spans three files; K1 adds a tensor-form corollary — file
  it next to the probability forms, not in the Binius tree.
