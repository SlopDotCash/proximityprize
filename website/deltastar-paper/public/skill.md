---
name: proximity-prize
description: Mine the open δ* / proximity-gap problem with Claude Code. Use when the user wants to contribute a verified "brick" (an exact-arithmetic probe or an axiom-clean Lean lemma) to the Ethereum Foundation proximity prize on lalalune/ArkLib. Self-updating — fetches the latest mission each run; produces ONE checked result (a win or an honest refutation) and opens a PR.
---
<!-- bootstrap-version: 2026-06-14.1 -->

# Mine the proximity prize with Claude Code

This skill is **self-updating**. The actual mission — current targets, the live issue, the
verification gate — lives in one canonical file that you fetch fresh **at the start of every
run**, so the campaign can move and you always run the latest without reinstalling.

## Step 0 — get the latest mission (do this first, every run)

```sh
curl -fsSL https://deltastar.computer/mission.md
```

Read what it prints and **follow it exactly** — it supersedes everything below this line.
Note its `mission-version` and report it at the end of the run.

**Self-freshness check (one line):** confirm this installed skill isn't stale —

```sh
curl -fsSL https://deltastar.computer/skill.md | grep bootstrap-version
```

If the remote `bootstrap-version` is newer than this file's (`2026-06-14.1`), tell the user
to refresh the skill itself by re-running the one-line installer:

```sh
mkdir -p ~/.claude/skills/proximity-prize && curl -fsSL https://deltastar.computer/skill.md -o ~/.claude/skills/proximity-prize/SKILL.md
```

(Mission changes don't need a reinstall — only a newer *bootstrap-version* does.)

## If you cannot reach the network — fallback essentials

The fetched `MISSION.md` is authoritative; this is only a safety net if `curl` fails. Mining
needs the network anyway (clone, PR), so prefer to get back online.

- **Goal:** add ONE *verified* brick to the open `δ*` / proximity-gap problem on
  `lalalune/ArkLib` (Ethereum's $1M prize, open ~25 years — you're not expected to solve it).
  A verified refutation counts as much as a proof.
- **Never fabricate:** no `sorry`, no axioms, no `: True := trivial`, no `float` "≈ 0", no
  "likely holds." A reproduced integer is not a verified inference — claim only the regime you
  computed; the wall is the worst-case sup-norm, not a fixed-`n` count.
- **Orient:** find the *current* tracking issue from the repo (don't trust a hardcoded
  number): read `Research/ProximityPrize/CLAUDE.md` + `Research/ProximityPrize/DISPROOF_LOG.md`
  (`grep -oE '#[0-9]{3}' Research/ProximityPrize/DISPROOF_LOG.md | sort | uniq -c | sort -rn | head`). The paper map
  is https://deltastar.computer/.
- **Get the repo, no fork needed for probes:** `git clone https://github.com/lalalune/ArkLib`.
- **Default brick = exact-arithmetic probe** (no Lean): reproduce one published integer from
  the relevant `scripts/probes/` probe first, then push it to the **prize regime** (constant
  rate ρ∈{1/2,1/4,1/8,1/16}, `q ≳ n·2^128`, smooth `μ_n`). It's a brick ONLY IF: stdlib-only,
  no `float`; the verdict **does not flip** at prize scale vs small `q`; a **second
  independent** implementation reproduces the integers; output is flushed/written to a file.
- **Lean brick:** compiles AND `#print axioms` = `[propext, Classical.choice, Quot.sound]`,
  no `sorryAx`.
- **Submit:** `gh auth login` + fork, new branch, stage only intended files (never
  `git add -A`), commit **as yourself, no AI co-author trailers**, `gh pr create --repo
  lalalune/ArkLib --fill`, post an honest note on the live issue. Then stop. The prize is open.
