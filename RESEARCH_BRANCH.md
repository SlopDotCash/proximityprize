# research/proximity-prize — the δ* campaign's home

This branch carries the FULL proximity-prize research corpus (Frontier rungs, workbench,
DISPROOF_LOG, dossier, kb, probes, websites) exactly as it stood pre-refactor
(tag `archive/pre-refactor-2026-07-09`), plus all campaign work going forward.

- **Campaign work lands HERE, not on `main`** (issue #499; see #466 for the research tracker).
- `main` keeps only the upstream-canonical library surface; never merge this branch into `main`.
- The paper websites deploy from this branch (Cloudflare workflows trigger on pushes here).
- Sync direction: merge `main` INTO this branch when library improvements land; never the reverse.

## Syncing main → research (IMPORTANT: corpus-preserving procedure)

A plain `git merge main` **silently deletes the campaign corpus**: main's refactor removed
~10k campaign files, and for any file this branch has not modified since the split, git merge
takes main's deletion. Never plain-merge. Procedure:

```bash
git merge fork/main --no-commit          # take main's changes
# resolve conflicts favoring THIS branch for campaign files / deploy workflows
# restore everything the merge would delete (NUL-safe; filenames contain unicode):
git ls-tree -r --name-only -z HEAD  > /tmp/head.z
git ls-files -z                     > /tmp/idx.z
# for every path in head.z missing from idx.z: git checkout HEAD -- <path>
bash scripts/update-lib.sh               # regenerate root over the union tree
git commit
```

(2026-07-10 sync `350267ae7` followed this; 10,380 paths restored.)
