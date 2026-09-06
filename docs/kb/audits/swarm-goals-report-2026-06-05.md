# Swarm Goals Report

Date: 2026-06-05

Baseline report: [`zkvm-total-verification-report-2026-06-05.md`](zkvm-total-verification-report-2026-06-05.md)

Primary ledger: [`proximity-prize/GRIND-LEDGER.md`](proximity-prize/GRIND-LEDGER.md)

## Purpose

This report is the current dispatch note for a swarm of subagents working on ArkLib verification
closure. Treat the baseline report as the status source of truth and this file as the coordination
brief for the next wave of work.

## Current Baseline

The active objective is to continue from
[`zkvm-total-verification-report-2026-06-05.md`](zkvm-total-verification-report-2026-06-05.md) and
close the proximity-prize keystone while preserving routine validation. The main mathematical route
is still `betaRec => CurveCoeffPolys`, then divisibility `Hlift H ∣ R`, gamma recentering, replacing
the trivial `beta_regular` path, proving `hcoeffPoly`, closing
`correlatedAgreement_affine_curves`, and only then de-tainting STIR, WHIR, and FRI downstream
soundness.

Current validation evidence on 2026-06-05 is green. A fresh `./scripts/validate.sh` run completed
the full Lean build, Data warning-budget gate, umbrella import check, docs integrity check, and KB
freshness check with:

```text
Build completed successfully (9061 jobs).
No ArkLib/Data non-sorry warnings found.
✓ All imports are up to date!
All documentation integrity checks passed.
Knowledge base generated files are up to date.
Knowledge base lint passed.
All requested validation checks passed.
```

The validation repair path was: shorten the single Data warning in
`ArkLib/Data/CodingTheory/GuruswamiSudan/BivariateVanishing.lean`, regenerate `ArkLib.lean`, regenerate
the KB artifacts with `extract_lean_citations.py`, `extract_declarations.py`, and
`find_dedup_candidates.py`, then confirm `check_generated.py` and `./scripts/validate.sh`.

The earlier transient untracked-scratch blocker
`ArkLib/Data/CodingTheory/InterleavedListSize.lean` was not present in the green run. If it reappears
and contains `trace_state`, `sorry`, or unscoped probe options, do not stage it as production code.

Multiple concurrent agents are editing and committing in this checkout. Always re-check the live
worktree before acting, and do not revert or overwrite other agents' changes.

## Recent Progress

- `HenselNumerator.lean` now exposes conditional consumer APIs:
  `assembledSeries_isRoot_of_coeff_succ_eval` and
  `βHensel_lift_identity_of_coeff_succ_eval`. These expose the P2 root/lift identity from the single
  successor residual instead of forcing downstream users through a theorem with a proof gap.
- `Curves.Assembly` builds again after the earlier unknown-namespace blocker was resolved.
- `GK16DegreeBudget.lean` adds the kernel-clean theorem
  `ArkLib.FRS.GK16.sum_rootMultiplicity_foldedWronskian_le`, chaining the folded-Wronskian degree
  bound to the root-multiplicity budget. `SubspaceDesign.lean` documents the remaining GK16 hard
  obligations.
- `InterleavedCode.lean` contains production projection lemmas, including
  `Code.relHammingDist_transpose_le` and
  `closeCodewordsRel_interleaved_transpose_mem_code`, with scoped warning suppressions where needed.
- Johnson-bound family refutation work stabilized the finite witness core in
  `FamilyRefutation.lean`, including the explicit codewords, membership characterization, pairwise
  distances, and `minDist_C : Code.minDist C = 1`.
- `LineDecodingRefutation.lean` is tracked and imported through `ArkLib.lean`; it refutes the false
  `lineDecodable_imp_epsMCA_le` statement.
- `CurvesBridge.lean` now has a degree-one canonical coefficient-polynomial supplier,
  `section5_strict_canonical_coeff_polys_for_RS_goodCoeffsCurve_finMapTwoWords_of_natCeil_complement_counting`,
  for the affine-line-to-§6 bridge. Direct build of
  `ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.CurvesBridge` passed.
- KB generation is current after running `extract_lean_citations.py`, `extract_declarations.py`,
  `find_dedup_candidates.py`, and `check_generated.py`.

## Goals

1. Close the proximity-prize keystone without duplicating already completed bridge work.
2. Assemble the real route from `betaRec` to `CurveCoeffPolys` by supplying the missing section-5
   data: matching points/cardinality, divisibility `Hlift H ∣ R`, gamma recentering, representative
   and degree hypotheses, plus the `Pz` and boundary facts required by the existing conditional
   theorem.
3. Replace the trivial in-tree `beta_regular` path with `betaRec`, prove `hcoeffPoly`, and close
   `correlatedAgreement_affine_curves` in `Curves.lean`.
4. De-taint downstream STIR, WHIR, and FRI round-by-round soundness only after the upstream theorem
   is genuinely closed.
5. Reduce remaining executable `sorry`s on active proof paths, prioritizing real proof discharge
   over wrapper APIs.
6. Keep the ArkLib/Data warning budget at zero non-sorry warnings and make `./scripts/validate.sh`
   green by fixing umbrella-imported build blockers.
7. Audit external admits, conjectures, and explicit hypotheses, separating acceptable formal
   interfaces from unresolved mathematical obligations.
8. Map claimed ArkLib theorems to the full zkVM verification stack and state which end-to-end
   components remain outside ArkLib.

## Subagent Instructions

Start every workstream by running:

```bash
git status --short --branch --untracked-files=all
git log --oneline --decorate -8
git diff --stat
git diff --cached --stat
```

Read the baseline report and this dispatch before editing. Work from the current checkout, preserve
concurrent changes, and do not revert files you did not change. Generated files such as `ArkLib.lean`
must be regenerated with repo scripts, not hand-edited. If adding, renaming, or deleting files under
`ArkLib/`, stage new paths before validation so the import-generation check sees them.

Use small targeted builds first, then full validation. A normal validation pass should be:

```bash
./scripts/update-lib.sh && git add ArkLib.lean
python3 ./scripts/kb/extract_declarations.py
python3 ./scripts/kb/find_dedup_candidates.py
python3 ./scripts/kb/check_generated.py
./scripts/validate.sh
```

If an untracked `ArkLib/Data/CodingTheory/InterleavedListSize.lean` exists, inspect it before doing
anything else. If it is still scratch code with `sorry` or `trace_state`, do not stage it; remove it
from `ArkLib/` or convert it into a production compiling module with no non-sorry warnings before
rerunning validation.

Every subagent report must include exact files, declarations, commands run, proof status, axiom
status where relevant, remaining assumptions, and blockers. Do not report a wrapper as proof closure
if it assumes the target theorem or the decisive witness.

## Suggested Workstreams

- Keystone integration: connect the existing `betaRec` bridge to section-5 data rather than
  re-proving the bridge.
- Divisibility and recentering: prove or thread `Hlift H ∣ R`, fix the `x₀`/gamma recentering issue,
  and feed the resulting hypotheses into the `Curves.lean` front door.
- Curve closure: replace `β_regular` with `betaRec`, prove `hcoeffPoly`, and discharge
  `correlatedAgreement_affine_curves`.
- Validation repair: keep `ArkLib/Data` at zero non-sorry warnings and remove transient untracked
  scratch files from the umbrella import path.
- Sorry audit: inventory executable `sorry`s on proof-critical paths and separate active gaps from
  abstract interfaces or documentation-only scaffolding.
- ZKVM map: extend the whole-stack analysis with theorem-to-component evidence and explicit
  statements of what ArkLib does not yet verify.
