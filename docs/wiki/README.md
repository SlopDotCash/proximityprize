# ArkLib Agent Wiki

This directory is the deeper companion to `AGENTS.md`.
Use `AGENTS.md` for the one-screen overview and this wiki for details that are too specific or
too changeable to keep at the repo root.
For reusable cross-cutting workflows that are not tied to one repo area, see
[`../skills/README.md`](../skills/README.md).

## Start Here

- [`quickstart.md`](quickstart.md) - canonical agent command and validation playbook.
- [`repo-map.md`](repo-map.md) - where to edit and how the main subtrees relate.
- [`generated-files.md`](generated-files.md) - derived outputs and their sources of truth.
- [`optiont-lift-coherence-walls.md`](optiont-lift-coherence-walls.md) - the per-branch-defeq
- [`deltastar-programme.md`](deltastar-programme.md) - **the δ* programme hub**: where every
  result, refutation, probe, and attack vector lives; the fast build path.
- [`census-programme.md`](census-programme.md) - the #357 δ* census architecture: theorem stack, empirical layer, conditional answer, working rules.
  technique for instance-path walls in run-unrolling proofs.
- [`blueprint-and-citations.md`](blueprint-and-citations.md) - blueprint workflow, paper
  references, and citation keys.
- [`knowledge-base.md`](knowledge-base.md) - when to use `docs/kb/` and how it relates to the
  agent wiki and bibliography.
- [`arklib-zkvm-boundary.md`](arklib-zkvm-boundary.md) - boundary between ArkLib proof-system
  verification and a whole-zkVM end-to-end theorem.
- [`zk-payment-channels.md`](zk-payment-channels.md) - imported zk-payment-channel proof
  artifact, reusable ArkLib infrastructure, and the concrete end-to-end roadmap.
- [`tower-fiber-theory.md`](tower-fiber-theory.md) - the #232 tower-fiber formal corpus
  (O35-O63): file map, the theory in one paragraph, recurring Lean gotchas.
- [`coding-theory-conventions.md`](coding-theory-conventions.md) - theorem-naming pattern,
  notation, type conventions, and tagged-sorry style used in
  `ArkLib/Data/CodingTheory/`.
- [`../kb/audits/open-problems-list-decoding-and-correlated-agreement.md`](../kb/audits/open-problems-list-decoding-and-correlated-agreement.md)
  - paper-to-ArkLib matrix for *Open Problems in List Decoding and Correlated Agreement*, with
    status labels, Lean references, and a follow-up roadmap.
- [`proximity-prize-leaderboard.md`](proximity-prize-leaderboard.md) - the machine-checked
  "bits of security" leaderboard for the ABF26 §6 toy protocol: how to submit a provable
  lower/upper bound, how `securityGap` is computed, and the current 64/116 anchors.
- [`honesty-audit.md`](honesty-audit.md) - playbook for finding unproven-but-presented-as-proven
  content: the laundering patterns the CI gates miss, how to detect them, and confirmed findings.
- [`additive-energy-attack.md`](additive-energy-attack.md) - the machine-checked reduction chain
  taking the Proximity Prize (#232) down to the additive energy of the smooth `2^k`-subgroup: file
  map, the sharp `E=3|G|(|G|-1)` theorem, the prize-regime anti-concentration data, and the single
  named open (Weil/sum-product) root.
- [`stir-issue-301.md`](stir-issue-301.md) - STIR #301 scratchpad: source trail, local theorem
  map, proof status, and the honest residuals for `stir_main` / `stir_rbr_soundness`.
- [`issue-329-tight-rbrks-patterns.md`](issue-329-tight-rbrks-patterns.md) - the target-carrying
  lift patterns from the Spartan tight rbr-KS campaign: why dropped lift data forces per-round
  error 1, the oracle-pinning keystone's two consumption directions, the kernel-leaf shape, the
  conjoin-at-unchanged-error recipe, guarded-terminal honesty, and the assembly mechanics.
- [`append-residuals-and-elaboration-patterns.md`](append-residuals-and-elaboration-patterns.md) -
  the #340 append-residual→discharge map (including the documented straightline-KS phase-1
  obstruction — do not attempt the direct extractor composition) and recurring elaboration
  walls: Pi-sum defeq bridges, the probe-bisection method, junk-completion for covering
  lemmas, and fold-generalization gotchas.

## Maintenance Contract

- `AGENTS.md` is the canonical root guide. `CLAUDE.md` is only a symlink.
- Keep one primary owner topic per page. The current pages are:
  - `quickstart.md` for commands, validation, and when to run which checks.
  - `repo-map.md` for repo structure and main work areas.
  - `generated-files.md` for derived outputs and source-of-truth rules.
  - `blueprint-and-citations.md` for blueprint workflow, references, and citation updates.
  - `knowledge-base.md` for when and how agents should use `docs/kb/`.
  - `arklib-zkvm-boundary.md` for the ArkLib-to-whole-zkVM theorem boundary.
  - `coding-theory-conventions.md` for naming/notation/type conventions in `CodingTheory/`.
  - `proximity-prize-leaderboard.md` for the ABF26 §6 bits-of-security leaderboard contract.
- Add new pages when a recurring topic no longer fits cleanly in an existing guide.
- If a PR changes commands, repo structure, generated-file behavior, or the paper workflow,
  update the matching page in the same PR, or add a new page when that is the cleaner split.
- Keep these files committed so worktrees and delegated agents see the same guidance.
- Promote recurring, repo-specific agent learnings here once they prove stable.
- Prefer links to canonical docs over copying their contents.

## Canonical Project Docs

- [`../../README.md`](../../README.md) - project overview.
- [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) - style, naming, docstrings, citations, and
  large contributions.
- [`../../ROADMAP.md`](../../ROADMAP.md) - planned directions.
- [`../../BACKGROUND.md`](../../BACKGROUND.md) - background references.
