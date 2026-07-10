# ⚠️ REPO REFACTOR IN PROGRESS — 2026-07-09 (READ BEFORE PUSHING TO `main`)

A structural refactor of this fork is being executed **right now** (tracking issue: **#499**).

## What is happening

`main` is being slimmed to library-canonical shape; the δ*/proximity-prize research campaign is
moving to the long-lived branch **`research/proximity-prize`** (created from the pre-refactor tip;
immutable snapshot tag: `archive/pre-refactor-2026-07-09`). Nothing is lost — every file that
leaves `main` remains on the research branch and in history.

- `ArkLib/Data/CodingTheory/ProximityGap/` on `main` returns to its upstream-canonical meaning
  (BCIKS20/DG25/AHIV22 paper formalizations + `Basic`/`Folding`/`MCAGenerator`/
  `ProximityGenerators` + `Errors`). The Frontier rungs, `_R*`/`_wf*`/QRWeil families, workbench,
  DISPROOF_LOG, dossier, kb corpus, probes, and all campaign tendrils (incl.
  `ProofSystem/Whir/MCAConjecture*`, prize-named `ToMathlib/*`) live on `research/proximity-prize`.
- ~75 MB of cruft (scripts/probes, root scratch, committed PDFs/archives, generated indexes) is
  being deleted from `main`.

## What YOU (agent) must do

1. **δ*/#466 campaign work: push to `research/proximity-prize`, NOT `main`.** New rungs, Frontier
   files, DISPROOF_LOG entries, kb notes — all of it. `main` CI will reject reintroduced campaign
   paths after the refactor lands.
2. **Do not "restore" files that disappear from `main`** — they moved by design. Check
   `research/proximity-prize` before concluding something was lost. Never merge the research
   branch back into `main`.
3. **Library work (protocols, Binius, OracleReduction, shared Data/ToMathlib)** continues on
   `main` as usual — rebase onto the refactored tip before pushing; expect large deletions in
   your merge base.
4. If your in-flight branch mixes both kinds of work, split it: library commits → `main`,
   campaign commits → `research/proximity-prize`.

## Status / coordination

- Plan and rationale: issue **#499** (full audit + phase plan). Progress is checklisted there.
- The δ* research tracker **#466** stays open and is unaffected — only the code's home changes.
- After the structural move, a quality/cleanup pass follows (consolidation, axiom/Residual
  triage, comment de-slop) — also tracked in #499.

This file will be removed when the refactor completes.
