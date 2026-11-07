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

The interactive explanation is `components/ProblemVisual.tsx`. Its arithmetic
is in `lib/rs-example.ts`: it enumerates all degree-below-four polynomials over
F17 on the order-eight subgroup. `npm test` checks the independently reproduced
candidate counts for every slider position and runs automatically before a build.
This demonstration illustrates ordinary list decoding, not the MCA guarantee.

Keep research claims tied to named theorems and their parameter ranges. The
[September 2026 claim audit](../kb/audits/research-site-claims-2026-09-06.md)
records the exact pins, collision bound, interpolation scope, and conditional
di Benedetto comparison used on the page. Do not turn conditional estimates or
best registered certificates into an unconditional state-of-the-art claim.

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

## Dependency advisories

This section covers both website projects, `website/deltastar-paper/` and
`website/truthmining/`. Run `npm audit` in each after every lockfile change. The
2026-10-28 refresh moved both to Next.js 15.5.28, sharp 0.35.5, KaTeX 0.18.10,
nanoid 3.3.20, source-map-js 1.2.2, and PostCSS 8.5.32 for the Tailwind plugin.
Truth Mining also moved to Tailwind CSS 4.3.3, because its 4.3.1 plugin pinned
PostCSS 8.5.15. KaTeX 0.18 adds a `katex-` prefix to internal classes such as
`base` and `strut`; Truth Mining styles only `.katex` and `.katex-display`.

Both audits still report the `postcss@8.4.31` copy that Next.js 15 pins exactly:
a high PostCSS entry (GHSA-qx2v-qp2m-jg93, GHSA-6g55-p6wh-862q,
GHSA-fxqj-rqcc-2cmp, GHSA-r28c-9q8g-f849) and a moderate `next` entry through it.
No Next 15 release removes the pin. Next 16.3 and later pin PostCSS 8.5.23, so
`npm audit fix --force` would make an unreviewed major upgrade. The residual does
not reach the published sites under these conditions:

- Each site uses `output: "export"`, and its workflow publishes only `out/` to
  Cloudflare Pages. No Next.js server, image optimization API, Server Actions,
  rewrites, middleware, or Pages Functions run in production.
- PostCSS runs only during builds. Its inputs are the sites' own stylesheets,
  Tailwind output, KaTeX's packaged stylesheet, and the font CSS that `next/font`
  generates for Truth Mining. The advisories need attacker-controlled CSS, such
  as a crafted `sourceMappingURL` comment or `</style>` text. HTTP requests to a
  development server cannot supply that input.

Recheck these conditions before a site processes third-party CSS, serves pages
with `next start`, or moves to Next 16.3 or later. A clean audit does not certify
third-party code.
