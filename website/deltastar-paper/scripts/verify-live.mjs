// A deploy is complete only when the production URL serves this artifact.
import { readFileSync } from "node:fs";
import { createHash } from "node:crypto";
const expected = JSON.parse(readFileSync(new URL("../out/deployment.json", import.meta.url), "utf8"));
const origin = process.argv[2] || "https://proximityprize.pages.dev";
for (let attempt = 0; attempt < 12; attempt++) {
  try {
    for (const [path, hash] of Object.entries(expected.files)) {
      const url = new URL(path === "index.html" ? "/" : `/${path}`, origin);
      url.searchParams.set("revision", expected.commit);
      const response = await fetch(url, { signal: AbortSignal.timeout(20000), cache: "no-store" });
      if (!response.ok) throw new Error(`${path}: HTTP ${response.status}`);
      const bytes = new Uint8Array(await response.arrayBuffer());
      if (createHash("sha256").update(bytes).digest("hex") !== hash) throw new Error(`${path}: deployed bytes differ`);
    }
    console.log(`Verified production HTML and onboarding files at ${origin} for ${expected.commit}`);
    process.exit(0);
  } catch (error) {
    console.log(`Readback ${attempt + 1}/12: ${error.message}`);
    if (attempt === 11) process.exit(1);
    await new Promise((resolve) => setTimeout(resolve, 10000));
  }
}
