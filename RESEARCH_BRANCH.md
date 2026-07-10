# research/proximity-prize — the δ* campaign's home

This branch carries the FULL proximity-prize research corpus (Frontier rungs, workbench,
DISPROOF_LOG, dossier, kb, probes, websites) exactly as it stood pre-refactor
(tag `archive/pre-refactor-2026-07-09`), plus all campaign work going forward.

- **Campaign work lands HERE, not on `main`** (issue #499; see #466 for the research tracker).
- `main` keeps only the upstream-canonical library surface; never merge this branch into `main`.
- The paper websites deploy from this branch (Cloudflare workflows trigger on pushes here).
- Sync direction: merge `main` INTO this branch when library improvements land; never the reverse.
