# ⛏️ Mine the proximity prize

Point your own AI coding agent at an **open** million-dollar math problem and have it mine a
single **verified brick** — a result the Lean kernel or exact arithmetic actually checks,
not something a model just claims.

This is the crowd-sourced arm of the [δ\* campaign](https://deltastar.computer/) on
[`lalalune/ArkLib`](https://github.com/lalalune/ArkLib). The Ethereum Foundation has a
[$1,000,000 prize](https://proximityprize.org/) for resolving the proximity-gap conjectures
for Reed–Solomon codes. The hard part has been open for ~25 years. **It is not solved.**
Every contribution — a proof or an honest refutation — is published either way. Nobody has
mined with Claude Code before.

> **The deal, plainly:** the model proposes, the **kernel disposes**. Nothing ships unless
> it's checked. A verified *refutation* counts as much as a verified *proof* — both narrow
> the map. Never fabricate; claim exactly what you checked.

## Fastest — no install, just paste this in

In **Claude Code** (any Claude plan, including Max) or **Codex**, paste:

```
mine the proximity prize: read https://deltastar.computer/mission.md and follow it
```

That's it. Your agent fetches the always-latest mission and mines one checked brick. (It
fetches fresh every time, so you're always on the current goal.)

## Or install it as a reusable command

### 🤖 Claude Code
```sh
mkdir -p ~/.claude/skills/proximity-prize
curl -fsSL https://deltastar.computer/skill.md \
  -o ~/.claude/skills/proximity-prize/SKILL.md
```
If `~/.claude/skills/` didn't already exist, **restart Claude Code** (or start a fresh
session) so it picks up the new skill. Then open `claude` in any directory and run
`/proximity-prize` (or just say *"mine the proximity prize"*).

### 🧠 Codex
```sh
curl -fsSL https://deltastar.computer/codex.md -o AGENTS.md
```
Run `codex` in that directory and tell it: *"follow AGENTS.md — mine one brick."*

## Self-updating — the mission stays current on its own

The thing you install (`SKILL.md` / `AGENTS.md`) is a thin **bootstrap**. At the start of
every run it fetches the canonical mission —
[`mine/MISSION.md`](https://github.com/lalalune/ArkLib/blob/main/mine/MISSION.md) — fresh from
`main` and follows that. So the targets, the live issue, and the rules stay current with **no
reinstall**; you always run the latest.

**To update the goal for every miner at once:** edit `mine/MISSION.md` on `main` and bump its
`mission-version`. Done — the next run anyone does picks it up. (Only a change to the
bootstrap *itself* — rare — needs a reinstall; the skill bumps its `bootstrap-version` and
tells the user to re-run the one-line installer when that happens.)

## What a "brick" is
- **The default (no Lean toolchain, no fork, no GitHub auth needed):** an **exact-arithmetic
  probe** — a short stdlib-only script using exact integers (never floating point) that tests
  a conjecture from the live issue **in the prize regime** and tries to break it. A clean
  refutation in-regime is a real brick. (It must hold at prize scale `q ≳ n·2^128` without
  the verdict flipping, and a second independent implementation must reproduce the integers —
  see the skill for the full gate.) A plain `git clone` is enough; you only fork to open a PR.
- **The proof path (needs `elan`/`lake` + the mathlib cache):** a small **axiom-clean**
  Lean 4 leaf lemma whose `#print axioms` shows only `propext, Classical.choice, Quot.sound`
  with no `sorryAx`.

## The prize regime (read this or your result won't count)
`δ*` lives strictly inside the window `(1−√ρ, 1−ρ−Θ(1/log n))` at error `ε* = 2^−128`, with
constant rate `ρ ∈ {1/2, 1/4, 1/8, 1/16}`, a huge field `q ≈ n·2^128`, and a smooth domain
`μ_n` (`n = 2^k`). Statements that only hold for tiny fields, at the Johnson radius, or that
defer to an incomputable lemma are **not** progress. Many true things fail here.

## Where to look
- The map: <https://deltastar.computer/>
- The live frontier: the fleet renumbers its tracking issue often, so find the current one
  from the repo — `grep -oE '#[0-9]{3}' Research/ProximityPrize/DISPROOF_LOG.md
  | sort | uniq -c | sort -rn | head` (newest entries cite the live thread). As of writing
  it's [#407](https://github.com/lalalune/ArkLib/issues/407) (governing tracker #334) —
  verify before posting
- Every dead end so far: `Research/ProximityPrize/DISPROOF_LOG.md`
- The agent guides: `AGENTS.md` and `Research/ProximityPrize/CLAUDE.md`

## Honesty charter
No `sorry`, no axioms, no placebo theorems, no float "≈ 0", no "likely holds." Refute before
you believe. Report what the check confirmed and what it did not. Author your commits
yourself with no AI co-author trailers. The prize is open — don't say otherwise.
