# Repository layout

The repository has four authored working areas: `ArkLib/` for Lean sources,
`docs/` for prose and reference material, `scripts/` for tooling and computational
probes, and `website/` for website sources. `external/` holds the existing
submodule. Only standard project, license, agent and Lean package files remain
at the root. `scripts/check-layout.py` rejects tracked files outside this layout.

## Source organization

| Previous path | Current path |
| --- | --- |
| `Research/ProximityPrize/` Lean files | `ArkLib/Research/ProximityGap/` |
| Research dossier, disproof log, guides and notes | `docs/research/proximity-gap/` |
| Research `kb/archive/` | `docs/research/proximity-gap/archive/` |
| `ProximityPrize/Extensions/` | `ArkLib/Extensions/` |
| `ProximityPrize/Compatibility/` | `ArkLib/Compatibility/` |
| `ProximityPrize.lean` | `ArkLib/Downstream.lean` |
| `ArkLibTest/` Lean files | `ArkLib/Tests/` |
| Test README | `docs/testing/README.md` |
| `home_page/` authored assets | `website/library/` |
| `blueprint/` | `website/blueprint/` |
| `mine/` | `docs/contributing/agent-workflows/` |
| Root background and roadmap | `docs/project/` |

Lean import paths follow the new file locations. Mathematical declaration
namespaces remain unchanged, including existing `ProximityPrize.*` APIs.
The canonical ArkLib source inventory and upstream provenance remain unchanged.
Knowledge-base catalogs cover the unified source tree, including research and
tests; catalog entries do not certify production status.
Separate Lake libraries keep classic downstream modules, research and acceptance
tests out of the production umbrella. Physical colocation does not make a test
or an experimental conditional result a production theorem.

## Removed scratch roots

The `_nubs_research/`, `_research_357/`, `_research_ll/`, and `scratchpad/`
directories are removed. Their eight unique files have organized homes:

- The F101 arithmetic checker and four orbit-arc probes live in `scripts/probes/`.
- The standalone F101 Lean witness lives in `scripts/probes/lean/`, outside the
  default build. Its assumptions and proof status are unchanged.
- The HBK extraction note lives in `docs/research/hbk-stepanov-extraction.md`.
- The byte-preserved Lam–Leung source extraction lives in
  `docs/research/sources/lam-leung-vanishing-sums.txt`.

Historical integration receipts and pinned GitHub links retain the paths of
the commits they describe. Do not rewrite those records to imply that a past
validation ran on today's layout. Obsolete branch-routing notices were
consolidated into [research history](../project/research-history.md).

## Website outputs

`website/library/` contains authored static assets. Website and blueprint builds
assemble generated output in ignored locations; the library deployment tree is
`build/site/`. Do not commit copied API documentation, blueprint HTML/PDF or site
export artifacts. See [blueprint and citations](blueprint-and-citations.md) and
[research site](research-site.md) for build commands.
