// Validate the actual static artifact, not just the Next compilation.
import { readFileSync, existsSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";

const site = fileURLToPath(new URL("../", import.meta.url));
const root = resolve(site, "../..");
const out = resolve(site, "out");
const html = readFileSync(resolve(out, "index.html"), "utf8");
const research = JSON.parse(readFileSync(resolve(site, "data/research.json"), "utf8"));
const fail = (message) => { throw new Error(message); };
if (!html.includes("https://proximityprize.pages.dev") || !html.includes("prize conjecture remains open")) fail("Missing canonical URL or open status");
if (/deltastar\.computer|deltastar-paper\.pages\.dev|lalalune\/ArkLib|degen mode/i.test(html)) fail("Obsolete site copy");
for (const row of research.records) if (!html.includes(row.radius)) fail(`Missing certificate radius ${row.radius}`);
const ids = [...html.matchAll(/\bid="([^" ]+)"/g)].map((m) => m[1]);
if (new Set(ids).size !== ids.length) fail("Duplicate section IDs");
for (const [, id] of html.matchAll(/href="#([^" ]+)"/g)) if (!ids.includes(id)) fail(`Broken anchor ${id}`);
for (const [, path] of html.replace(/<script[\s\S]*?<\/script>/g, "").matchAll(/https:\/\/github.com\/SlopDotCash\/proximityprize\/blob\/[a-f0-9]+\/([^"< ]+)/g)) {
  if (!existsSync(resolve(root, path))) fail(`Missing research source: ${path}`);
}
const assets = new Set([...html.matchAll(/(?:src|href)="([^" ]*\/_next\/[^" ]+)"/g)].map((m) => m[1]));
for (const asset of assets) {
  const local = asset.slice(asset.indexOf("/_next/") + 1);
  if (!existsSync(resolve(out, local))) fail(`Missing exported asset: ${asset}`);
}
const files = { "index.html": html };
for (const [name, source, marker] of [
  ["mission.md", "mine/MISSION.md", "mission-version:"],
  ["skill.md", "mine/claude/proximity-prize/SKILL.md", "bootstrap-version:"],
  ["codex.md", "mine/codex/AGENTS.md", "bootstrap-version:"],
]) {
  const value = readFileSync(resolve(out, name), "utf8");
  if (value !== readFileSync(resolve(root, source), "utf8") || !value.includes(marker)) fail(`Stale onboarding file: ${name}`);
  if (/deltastar\.computer|lalalune\/ArkLib/.test(value)) fail(`Obsolete onboarding destination: ${name}`);
  files[name] = value;
}
const manifest = { commit: research.sourceCommit, files: Object.fromEntries(Object.entries(files).map(([name, value]) => [name, createHash("sha256").update(value).digest("hex")])) };
writeFileSync(resolve(out, "deployment.json"), JSON.stringify(manifest, null, 2) + "\n");
console.log(`Static export verified: ${assets.size} assets, four research rows, source links, anchors, and onboarding files.`);
