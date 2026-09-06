// Publishes the canonical miner files (single source of truth in /mine) to the
// site's public/ dir so they're served at the domain root:
//   proximityprize.pages.dev/mission.md   (the always-latest mission)
//   proximityprize.pages.dev/skill.md     (Claude Code skill bootstrap)
//   proximityprize.pages.dev/codex.md     (Codex bootstrap)
// Runs automatically before `dev` and `build` (npm pre* hooks). Generated files
// are committed; /mine/* stays the only edited copy.
import { copyFileSync, mkdirSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";

const here = dirname(fileURLToPath(import.meta.url));
const repoRoot = resolve(here, "../../.."); // website/deltastar-paper/scripts -> repo root
const pub = resolve(here, "..", "public");
mkdirSync(pub, { recursive: true });

const files = [
  ["mine/MISSION.md", "mission.md"],
  ["mine/claude/proximity-prize/SKILL.md", "skill.md"],
  ["mine/codex/AGENTS.md", "codex.md"],
];

for (const [src, dst] of files) {
  copyFileSync(resolve(repoRoot, src), resolve(pub, dst));
  console.log(`copy-mine: ${src} -> public/${dst}`);
}
