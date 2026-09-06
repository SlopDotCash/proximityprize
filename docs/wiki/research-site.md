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

## Continuous deployment

`.github/workflows/deltastar-cloudflare.yml` builds pull requests without deployment
secrets. Changes to the site, canonical onboarding, research, research notes, or
probes trigger it. Main pushes build and upload one artifact, then a separate job
publishes those exact files to `proximityprize.pages.dev`. Manual runs deploy only
when the selected branch is `main`. Production deployments are serialized and
are not cancelled halfway through an upload.

Configure in `SlopDotCash/proximityprize`:

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
revert to main. The same build, deployment, and readback checks apply.

The old `deltastar-paper.pages.dev` project is separate. Its redirects can only be
changed through the account that owns it; this workflow never deploys to it.
