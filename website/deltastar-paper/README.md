# Proximity Prize website

Live site: https://proximityprize.pages.dev

A concise research summary with links to the source evidence. Built with Next.js
as a static export. The source directory keeps its historical name so existing
GitHub Pages builds continue to work.

```sh
npm ci
npm run dev
npm run build
```

Python 3 is required. Before development and build, the site copies the canonical
onboarding files from `mine/` and reads the certificate registry into ignored
`data/research.json`. Update the research prose in `app/page.tsx`; edit certificate
records in `scripts/probes/hdd_certificates.py` at the repository root. The table
selects the best registered certificate for each rate. It does not run the
mathematical certificate verifier or certify a new research result.

`npm run build` validates the export and writes a deployment manifest.
`PAGES_BASE_PATH=/deltastar` supports the existing GitHub Pages export; leave it
unset for Cloudflare. Onboarding links respect the same base path.

For publishing, credentials, verification, and rollback, see
[`docs/wiki/research-site.md`](../../docs/wiki/research-site.md).
