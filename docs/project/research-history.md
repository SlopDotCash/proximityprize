# Research history

The campaign originally developed in the ArkLib fork on the
`research/proximity-prize` branch. A July 2026 proposal split research from the
upstream library; its refactor notices and one-way synchronization instructions
are historical and no longer apply.

The canonical repository is now `SlopDotCash/proximityprize`, with both the
library and research campaign integrated on `main`. Develop feature branches
from current `origin/main` and open pull requests against this repository.
Never publish changes to `Verified-zkEVM/ArkLib`.

The current layout puts reusable library modules, downstream extensions,
research modules and acceptance tests under `ArkLib/`, with separate Lake
libraries and import boundaries. Research notes live in `docs/research/`,
probes in `scripts/probes/`, and website sources in `website/`.
See the [repository map](../wiki/repo-map.md) and
[research dossier](../research/proximity-gap/DOSSIER.md) for current guidance.
Git history retains the original branch notices and migration records.
