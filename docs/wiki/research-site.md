# Research website publishing

The public research site is https://proximityprize.pages.dev. Source remains in
`website/deltastar-paper/`; Cloudflare project `proximityprize` uses production
branch `main` in the project's configured Cloudflare account.

## Source and build

Edit `app/page.tsx` for research prose. The prebuild script reads the exact
certificate registry in `scripts/probes/hdd_certificates.py`, selects the best
registered agreement threshold at each rate, and writes ignored
`data/research.json` with the build's source commit. Rounded radii are presentation
values. Registry extraction does not rerun the mathematical verification; new
records must be checked by the research workflow before publication.

The canonical onboarding files are `mine/MISSION.md`,
`mine/claude/proximity-prize/SKILL.md`, and `mine/codex/AGENTS.md`. The prebuild
copies them into the site's committed `public/` files. Commit regenerated copies
when changing those sources. Do not edit the copies directly.

Run `npm ci && npm run build` from `website/deltastar-paper/` with Node 22 and
Python 3. The postbuild checks source paths, page anchors, static assets, research
rows, onboarding equality, and obsolete destinations. It writes
`out/deployment.json` with the source SHA and public-file hashes. Generated
`out/`, `.next/`, and `data/research.json` must not be committed.

## Publishing with Wrangler

The default publishing path uses a local authenticated Wrangler session:

```sh
cd website/deltastar-paper
npm ci && npm run build
npx wrangler@4.129.0 pages deploy out --project-name=proximityprize --branch=main
node scripts/verify-live.mjs
```

`.github/workflows/deltastar-cloudflare.yml` builds and validates pull requests
and main pushes, then uploads the export as an artifact. Changes to the site,
canonical onboarding, research, research notes, or probes trigger it. These
routine builds do not require Cloudflare credentials.

For optional hosted deployment, manually dispatch the workflow on `main` with
`deploy` enabled. Its default is false. Production deployments are serialized
and are not cancelled halfway through an upload. The deployment job publishes
the exact validated build artifact and verifies production content.

Only when enabling hosted deployment, configure in `SlopDotCash/proximityprize`:

- Actions secret `PROXIMITYPRIZE_CLOUDFLARE_API_TOKEN`: a Cloudflare API token with
  Account / Cloudflare Pages / Edit, limited to the deployment account.
- Actions variable `PROXIMITYPRIZE_CLOUDFLARE_ACCOUNT_ID`: the owning account ID.
- Environment `proximityprize-pages`: production deployment history. Apply repository
  environment rules if approval is required by the maintainers.

The preflight checks account access, exact subdomain, and production branch. After
upload, `scripts/verify-live.mjs` checks the production HTML and all three onboarding
files against the built hashes. A green build alone does not prove publication.
See [Cloudflare's CI guide](https://developers.cloudflare.com/pages/how-to/use-direct-upload-with-continuous-integration/).

For rollback, revert the site change on a feature branch and merge the reviewed
revert to main. Rebuild and publish the reverted source with Wrangler, then run the readback check.

The old `deltastar-paper.pages.dev` project is separate. Its redirects can only be
changed through the account that owns it; this workflow never deploys to it.
