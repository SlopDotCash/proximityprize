# ProximityGap — agent guide

This directory holds the **library formalization of the proximity-gaps literature** and the
protocol-facing abstractions consumed by FRI/STIR/WHIR soundness:

- `BCIKS20/` — Ben-Sasson–Carmon–Ishai–Kopparty–Saraf, *Proximity Gaps for Reed–Solomon Codes*
  (affine lines/spaces, curves, list decoding, error bounds, weighted agreement).
- `DG25/`, `AHIV22*`, `BCKHS25/`, `GK16*`, `CS25*` — further proximity/list-decoding papers.
- `Basic`, `Folding`, `MCAGenerator`, `ProximityGenerators`, `Errors` — the abstractions and
  ε-accounting API protocol soundness proofs import.

**The δ*/proximity-prize research campaign does NOT live here.** It moved to the branch
`research/proximity-prize` (2026-07-09 refactor, issue #499; full pre-refactor snapshot at tag
`archive/pre-refactor-2026-07-09`). Push campaign work — Frontier rungs, workbench, DISPROOF_LOG,
dossier, kb notes — to that branch, never to `main`. A number of campaign-conditional files remain
here temporarily because WHIR/STIR soundness still depends on them (see #499 "pinned-back" list);
they are flagged for the consolidation pass — do not grow them.

Keep this directory upstream-shaped: paper-keyed subdirectories, one development per paper,
no session logs or narrative markdown.
