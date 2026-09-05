# Blueprint and Citations

Use this page when a change is paper-driven, adds a new reference, or changes long-lived
formalization structure.

## Source Of Truth

- [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) is canonical for style, docstrings, naming,
  and citation policy.
- `blueprint/src/` contains blueprint sources.
- `blueprint/web/` and `blueprint/print/` are outputs.
- `BACKGROUND.md` is a lightweight reference list, not the detailed theory source.

## When To Reach For The Blueprint

- New proof systems or other substantial formalization efforts.
- Paper-driven API or design work that spans several files.
- Changes that need shared references, BibTeX entries, or published docs.

For substantial contributions, discuss the blueprint-first workflow described in
[`../../CONTRIBUTING.md`](../../CONTRIBUTING.md).

## Citation Workflow

1. Cite papers in Lean docstrings by citation key, for example `[BCIKS20]`.
2. Give the Lean file a `## References` section in its module docstring.
3. Add the matching BibTeX entry to `blueprint/src/references.bib`.
4. For durable paper context, create or update `docs/kb/papers/KEY.md` for the same citation key.
5. Prefer public paper titles, venues, DOIs, or URLs in shared docs rather than pointing readers
   to private or local notes.

## Knowledge Base Mapping

- `blueprint/src/references.bib` is the bibliographic source of truth.
- `docs/kb/papers/KEY.md` is the preferred repository-local landing page for a cited paper key.
- `docs/kb/sources/KEY/metadata.yml` records source provenance and optional local artifacts.
- `docs/kb/_generated/lean-citations.json` is the generated map from Lean files to cited keys.

## Build And Publish Checks

```bash
DISABLE_EQUATIONS=1 lake build ArkLib:docs
./scripts/build-web.sh
```

If blueprint output matters and `leanblueprint` is missing:

```bash
python3 -m pip install leanblueprint
```

### Building the blueprint locally without TeX

`leanblueprint web` (plasTeX) resolves every `\input` through the external `kpsewhich`
binary. On a machine without a TeX distribution the build "succeeds" but every chapter is an
empty ~5KB shell (18 `File not found` warnings) — a vacuous gate. Two fixes:

- Install TeX (what CI does via the `texlive-full` container; `leanblueprint pdf` also needs it).
- Or shim `kpsewhich` with a script that searches `$TEXINPUTS` then the cwd, trying
  `name`, `name.tex`, `name.sty`; put it on `PATH` before running `leanblueprint web`.
  With the shim the local web build produces full chapters (`chap-proof_systems.html` ≈ 300KB,
  not ≈ 5KB) and the genuine content warnings (missing bib keys, unsupported macros) become
  visible. `pip install pygraphviz` needs `brew install graphviz` headers
  (`CFLAGS=-I$(brew --prefix graphviz)/include LDFLAGS=-L$(brew --prefix graphviz)/lib`).

Sanity probe after any blueprint build: `wc -c blueprint/web/chap-*.html` — chapters in the
single-digit-KB range mean the inputs did not resolve and the build was vacuous.

### Deployment configuration

GitHub Pages uses `.github/workflows/docs.yml` on `main`; the repository must
have Pages enabled with GitHub Actions as its build source. The workflow builds
the Lean library, API documentation, and blueprint before deploying.

The Cloudflare workflows watch their website directories on `main` and also
accept manual dispatch on `main`. Pushes build and upload the static site artifacts.
Publish locally using an authenticated Wrangler session from the site directory:

```bash
npm ci
npm run build
npx wrangler pages deploy out --project-name=deltastar-paper --branch=main
# Use --project-name=truthmining from website/truthmining instead.
```

GitHub-hosted deployment is opt-in through the manual `deploy` input and requires
repository secrets `CLOUDFLARE_API_TOKEN` and `CLOUDFLARE_ACCOUNT_ID`. A local
Wrangler OAuth login is not available on GitHub runners. Push filters and
production deployment guards must use the same branch.
