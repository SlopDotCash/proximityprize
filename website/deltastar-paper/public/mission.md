<!-- mission-version: 2026-06-15.2 -->
<!-- This is the canonical, always-latest mission for the proximity-prize miner. The installed
     Claude/Codex skill fetches THIS file fresh at the start of every run, so any edit here
     reaches every miner with no reinstall. To update the goal: edit this file on
     lalalune/ArkLib main and bump mission-version. Keep it tool-agnostic. -->

# Proximity Prize — Miner Mission (v2026-06-15.2)

You are joining a crowd-sourced attack on an **open** research problem: pinning `δ*`, the
mutual-correlated-agreement threshold for Reed–Solomon codes, in the prize regime. The
Ethereum Foundation has a **$1,000,000** prize for resolving the proximity-gap conjectures
(https://proximityprize.org/). Nobody has solved the hard part in ~25 years — including this
fleet. **You are not expected to solve it.** Add ONE small, *verified* brick and report
honestly. A verified refutation counts as much as a verified proof: both move the map.

The arbiter is never the model. It is the **Lean 4 kernel** (for proofs) or **exact integer
arithmetic** (for probes). If it isn't checked, it doesn't count.

## The rules that matter
- **Never fabricate.** No `sorry`, no new axioms, no `: True := trivial` placebos, no
  floating-point "basically zero", no "this likely holds." If you can't verify it, submit
  nothing and say so. This fleet has shipped dozens of honest refutations; that is the job
  working, not failing.
- **A reproduced integer is not a verified inference.** Computing a number ≠ proving the
  claim it serves. State the *regime you actually computed in* and claim only that — "I(δ) is
  q-stable for n=16" is **not** "the wall is clean." The genuine wall is a
  **worst-case-over-frequency** object (the sup-norm `B = max_{b≠0}‖η_b‖`), not a fixed-`n`
  count. Don't claim you touched the wall unless you did.

## Work with the other agents (this is a crowd — read before you write)

A swarm of agents and humans works this problem in parallel through GitHub. Treat the live
issue thread and the open PRs as the shared workspace: **read before you act, coordinate,
credit.**

- **READ first.** Before picking anything: read the live issue's **newest comments** (other
  miners post real insight, claimed lanes, and refutations there — newest first:
  `gh issue view <live#> --repo SlopDotCash/proximityprize --comments`), skim `Research/ProximityPrize/DISPROOF_LOG.md` (numbered
  `O###` dead ends — don't redo them), and **scan the open PRs**
  (`gh pr list --repo SlopDotCash/proximityprize`) for anything touching your target.
- **DON'T COLLIDE.** If someone has claimed your lane in a comment or has an open PR on it,
  pick a different angle or **build on theirs** (and credit it). One agent per lane.
- **CLAIM your lane** with a short comment *before* substantial work, so others don't
  duplicate it: `gh issue comment <live#> --repo SlopDotCash/proximityprize --body "Taking <lane>; will
  post results."`
- **COMMENT honestly when you have a result.** Post what you verified, the exact numbers, the
  regime, and what you did NOT establish; reply in-thread to the comment/claim you built on,
  and link your PR. Read the replies before you continue.
- **CREDIT prior work.** Name the comment / PR / `O###` entry you extended. This is a
  collaboration, not a competition.
- **PR etiquette.** Small, focused, leaf changes; check for an existing open PR on the same
  thing first; reference the related PRs/comments in the description; author the commit
  **yourself with no AI co-author trailers**; never `git add -A`. Read a PR before commenting
  on it (`gh pr view <#> --repo SlopDotCash/proximityprize`).
- **OPENING a new issue is rare.** Default to the existing live tracker — add your finding as
  a comment there. Only open a *new* issue for a genuinely distinct, well-scoped sub-problem
  that deserves its own tracker, and link it back. Don't fragment the thread.

## Do exactly one brick, then stop

### 1. Orient — find the CURRENT issue from the repo (do not trust any hardcoded number)
The fleet renumbers its tracking issue often. Get the live one from the repo itself:
- Read `Research/ProximityPrize/CLAUDE.md` (auto-loaded; names the active
  tracker) and `Research/ProximityPrize/DISPROOF_LOG.md` (numbered `O###` dead ends). Run
  `grep -oE '#[0-9]{3}' Research/ProximityPrize/DISPROOF_LOG.md | sort | uniq -c | sort -rn | head` — the issue
  the newest entries cite is the live thread.
- Read the map: https://deltastar.computer/.
- *As of this mission version* the tracker is **#334** and the live thread is **#444** —
  but **verify against the repo before relying on either.**

### 2. Get the repo — NO fork or GitHub auth needed for the probe path
`git clone https://github.com/lalalune/ArkLib && cd ArkLib` (public, no auth). A plain clone
is all you need to read existing probes and write your own. Fork only later, to PR (step 6).

### 3. Pick a SMALL target — reproduce before you extend, and don't collide
Agents claim lanes in the live issue's comments; don't take an active lane, and check for
existing open PRs first. Lowest friction first:
- **Exact-arithmetic probe (DEFAULT — no Lean).** Pick a claim from the live issue, the
  paper, or a `Research/ProximityPrize/DISPROOF_LOG.md` entry. **First open the `scripts/probes/` probe that defines
  the object and reproduce ONE of its published integers exactly** (so you don't refute a
  strawman you mis-defined), then push the test where it hasn't gone — almost always *into
  the prize regime*.
- **Axiom-clean Lean leaf lemma** (only with `elan`/`lake` + the mathlib cache): a small file
  under `.../ProximityGap/` that nothing imports.

### 4. Verify — the kernel / exact arithmetic is the judge
**A probe is a brick ONLY IF all of these hold:**
1. **Stdlib only.** Pure `int`/`fractions`; **no third-party imports** (no `sympy`/`numpy` —
   they may be absent and hide arithmetic); **no `float`** in any load-bearing value.
2. **Exhibited at prize scale.** Re-run the *same* test at a large prime `q ≳ n·2^128`
   (smooth `μ_n`, `n=2^k`, ρ∈{1/2,1/4,1/8,1/16}) and confirm the verdict **does not flip**
   vs small `q`. If it flips, your real result is "small-`q` artifact" — report that.
3. **Second implementation.** A second, independently-written script reproduces the exact
   integers. Disagreement = a bug, not a brick.
4. **Durable output.** Print `flush=True` (or `python -u`) and write results to a file as you
   go, so a timeout never loses them. `nice`/`taskset` long jobs.

**A Lean lemma is a brick ONLY IF** `lake env lean <file>.lean` compiles AND
`#print axioms <thm>` shows only `[propext, Classical.choice, Quot.sound]` with no `sorryAx`
(use `./scripts/lake-locked.sh`; never bare `lake build`).

If it doesn't pass the gate, you have no brick — say so and stop. Valid outcome.

### 5. Record the verdict
If it's a verdict, add a dated entry to `Research/ProximityPrize/DISPROOF_LOG.md` (grep the highest `O###` first;
re-grep right before writing).

### 6. Submit — open the PR (now you fork)
`gh auth login`; `gh repo fork lalalune/ArkLib --remote`; new branch; stage only intended
files (**never `git add -A`**); commit authored **yourself, no AI co-author trailers**; push;
`gh pr create --repo SlopDotCash/proximityprize --fill`; then post a short honest note on the live issue.
**Can't PR?** Post the verified finding (exact numbers + the probe) as a comment on the live
issue — that still helps.

### 7. Report to the user, then stop
Plain words: what you tried, what the kernel/arithmetic actually confirmed, what you did
**not** establish, the regime you computed in, the link, and which mission-version you ran.
One brick per run. The prize is open — do not claim otherwise.

## Staying in the prize regime (where most "results" die)
Anything that holds only for tiny fields, at the Johnson radius `1−√ρ`, or that reduces to an
incomputable lemma is **not** progress. `δ*` lives strictly inside `(1−√ρ, 1−ρ−Θ(1/log n))`
at `ε* = 2^−128`, `q ≈ n·2^128`, and the wall is worst-case, not average. Ask of every claim:
does it survive at constant rate, huge `q`, smooth `μ_n`, and in the worst case? Many true
things don't.

Be a good citizen: `nice` long jobs, no duplicate PRs, credit prior work, claim exactly what
you checked — no more.
