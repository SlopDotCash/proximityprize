# Standalone cleanup reassessment — 2026-08-16

This is the current-main reassessment of standalone issue
[#2](https://github.com/SlopDotCash/proximityprize/issues/2). The issue body preserves the
2026-07-09 ArkLib-fork audit, but its proposed branch architecture predates the dedicated
`SlopDotCash/proximityprize` repository. The standalone migration deliberately made `main` the home of
the Proximity Prize corpus, so moving the campaign back to a retired research branch is no longer
an active cleanup target.

## Measured current state

Audited at `b72890393a68745ecc43f6b39470509b630c7192`:

| surface | historical issue estimate | standalone base | after bounded cleanup |
|---|---:|---:|---:|
| all tracked files | about 12,170 | 8,600 | 8,597 |
| `scripts/probes/**` | 4,724 files, about 30 MB | 410 files, 3.5 MB | 409 files, 3.5 MB |
| `ProximityGap/**` | 4,259 files | 4,994 files | 4,993 files |
| `ProximityGap/Frontier/**` | 2,341 files | 3,079 files | 3,078 files |
| `docs/kb/**` | 1,173 files | 1,481 files | 1,480 files |

The larger research surfaces are expected in the dedicated repository and are not themselves
cruft. The named root scratch files, committed PDFs, `.bak`, `.patch`, `.wip`, AppleDouble, and
mojibake-path artifacts from the historical audit are absent from current `main`.

## Bounded cleanup completed by this reassessment

- Removed two raw issue-357 JSON archives (about 1.5 MB). Their durable mathematical synthesis is
  `docs/kb/deltastar-357-compiled-knowledge.md`; the raw discussion remains public and recoverable
  from the historical issue and git history.
- Removed the empty `scripts/probes/_ckpt_466r11_leancheck.txt` checkpoint.
- Removed the imported `Frontier/Template.lean` placeholder. It still referred to historical
  issue #334, compiled a vacuous `example : True`, and disagreed with the README's nonexistent
  `_TEMPLATE.lean` path. New lanes should start from a nearby minimal module instead.
- Regenerated `ArkLib.lean` so the deleted template is no longer an umbrella import.

## Explicitly deferred

- `docs/kb/_generated/declarations.json` (about 39 MB) and `dedup-report.md` remain tracked because
  current KB validation treats them as generated source-of-truth artifacts. Removing them requires
  a separate workflow/consumer change, not an isolated deletion.
- The 409 remaining exact probes are reproducibility evidence for theorem and no-go claims. Any
  future pruning must first map each probe and captured output to its surviving claim.
- Physical relocation of the campaign is superseded by the standalone-repository decision.
- Upstream carve-outs remain Phase 4 work and should be proposed as small dependency-closed diffs,
  not by replaying the historical fork-wide move plan.

## Reproduction

```bash
git ls-files | wc -l
git ls-files 'scripts/probes/**' | wc -l
git ls-files -z 'scripts/probes/**' | xargs -0 du -ch | tail -n 1
git ls-files 'ArkLib/Data/CodingTheory/ProximityGap/**' | wc -l
git ls-files 'ArkLib/Data/CodingTheory/ProximityGap/Frontier/**' | wc -l
git ls-files 'docs/kb/**' | wc -l
```
