# Knowledge Base Scripts

These scripts maintain the generated indexes that support `docs/kb/`.

They are intentionally lightweight and use only the Python standard library.

## Scripts

- `sync_from_bib.py` - export `website/blueprint/src/references.bib` into
  `docs/kb/_generated/references.json`
- `extract_lean_citations.py` - scan Lean sources in `ArkLib/`, `Research/`, and `ProximityPrize/` and generate
  `docs/kb/_generated/lean-citations.json`
- `extract_declarations.py` - scan Lean sources in `ArkLib/`, `Research/`, and `ProximityPrize/` and generate
  `docs/kb/_generated/declarations.json`, a catalog of every declaration
  (file, line, kind, namespace, name, brief signature, docstring head)
- `find_dedup_candidates.py` - derive `docs/kb/_generated/dedup-report.md`
  from the catalog: same-short-name groups across files + cross-file
  near-duplicate docstrings, a review aid for spotting duplication in PRs
- `regenerate.py` - refresh all generated indexes and scaffold missing cited paper pages
- `check_generated.py` - check that the committed generated indexes match the current checkout
- `scaffold_paper.py KEY` - create a stub paper page and source metadata file for `KEY`
- `lint.py` - validate paper-page structure and report cited keys without paper pages
- `review_context.py` - resolve citation keys, KB paper pages, and external URLs for review
  comments

## Usage

Run from the repo root:

```bash
uv run --no-project --python 3.12 python ./scripts/kb/sync_from_bib.py
uv run --no-project --python 3.12 python ./scripts/kb/extract_lean_citations.py
uv run --no-project --python 3.12 python ./scripts/kb/extract_declarations.py
uv run --no-project --python 3.12 python ./scripts/kb/find_dedup_candidates.py
uv run --no-project --python 3.12 python ./scripts/kb/regenerate.py
uv run --no-project --python 3.12 python ./scripts/kb/check_generated.py
uv run --no-project --python 3.12 python ./scripts/kb/lint.py
uv run --no-project --python 3.12 python ./scripts/kb/review_context.py --files ArkLib/ProofSystem/Fri/Spec/SingleRound.lean --format review
```

## Intended Workflow

1. Update `website/blueprint/src/references.bib`.
2. Update the paper page when the PR changes ArkLib's interpretation or use of that paper.
3. Run `uv run --no-project --python 3.12 python ./scripts/kb/regenerate.py`.
4. Review and commit the tracked indexes and any scaffolded paper or source pages with the
   source changes.

The read-only [KB workflow](../../.github/workflows/kb-generated.yml) verifies the committed
state on relevant PRs and pushes to `main`. It can also run on demand.

## Review Workflow Notes

`review_context.py` emits a comment body shaped for `.github/workflows/review.yml`.
The current workflow accepts three sources of review context:

- explicit `External:` URLs from the review comment;
- explicit `Internal:` repo paths from the review comment;
- free-form `Comments:` from the review comment.

Use `review_context.py` locally to infer citation-backed `External:` and `Internal:` entries from
changed Lean files or explicit BibTeX keys, then paste its output into a `/review` comment.
