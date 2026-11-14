# Swarm Subagent Dispatch Report

Date: 2026-06-05

Root guide: [`../../../AGENTS.md`](../../../AGENTS.md)

Baseline status report:
[`zkvm-total-verification-report-2026-06-05.md`](zkvm-total-verification-report-2026-06-05.md)

Current coordination report:
[`swarm-goals-report-2026-06-05.md`](swarm-goals-report-2026-06-05.md)

Primary proximity ledger:
[`proximity-prize/GRIND-LEDGER.md`](proximity-prize/GRIND-LEDGER.md)

## Purpose

This is the compact dispatch report for subagents working in the ArkLib checkout. It combines the
root agent instructions with the current proof goals and validation discipline so independent
workers can start without relying on ephemeral chat context.

## Operating Rules

Start with the root guide and project overview. `AGENTS.md` is the canonical root guide, and
`README.md` gives the project overview. `ArkLib.lean` is generated; regenerate it with repo scripts
instead of editing it by hand. Do not edit derived outputs such as `.lake/`, generated blueprint
output, dependency graphs, or home-page docs. If adding, renaming, or deleting files under
`ArkLib/`, stage the new paths before validation so the import generator can see them. Existing
`sorry` blocks are known to exist, so distinguish pre-existing proof gaps from new regressions.

Begin every workstream by checking the live checkout:

```bash
git status --short --branch --untracked-files=all
git log --oneline --decorate -8
git diff --stat
git diff --cached --stat
```

Preserve concurrent changes. Do not revert, delete, or overwrite work you did not make unless the
owner explicitly asks for that. Work in small proof-facing increments, use targeted `lake build`
commands first, and only then run the full validation path.

## Validation Path

The routine gate is:

```bash
./scripts/validate.sh
```

When imports or KB artifacts need refreshing, use:

```bash
./scripts/update-lib.sh && git add ArkLib.lean
python3 ./scripts/kb/extract_lean_citations.py
python3 ./scripts/kb/extract_declarations.py
python3 ./scripts/kb/find_dedup_candidates.py
python3 ./scripts/kb/check_generated.py
./scripts/validate.sh
```

Use `./scripts/validate.sh --lint` only when Lean style linting is part of the task. Use
`./scripts/validate.sh --docs` for docstring or docs work. Use `./scripts/validate.sh --site` only
when touching `website/blueprint/` or `website/library/`.

## Goals

1. Close the proximity-prize keystone without duplicating completed bridge work.
2. Assemble the real route from `betaRec` to `CurveCoeffPolys` by supplying the remaining section-5
   extraction/setup hypotheses: matching points, matching-set cardinality and weight bounds,
   representative data, degree bounds, decoded-family specialization, `Pz`, and boundary facts.
3. Prove or thread the divisibility obligation `Hlift H ∣ R`.
4. Fix the gamma recentering issue for nonzero centers.
5. Replace the trivial in-tree `beta_regular` route with the real `betaRec` route.
6. Prove `hcoeffPoly` and close `correlatedAgreement_affine_curves` in `Curves.lean`.
7. De-taint downstream STIR, WHIR, and FRI soundness only after upstream correlated-agreement
   closure is real.
8. Reduce executable `sorry`s on active proof paths, prioritizing genuine proof discharge over
   wrapper APIs.
9. Keep `ArkLib/Data` at zero non-sorry warnings and make `./scripts/validate.sh` green.
10. Audit admits, conjectures, and explicit assumptions, separating accepted external interfaces
    from unresolved mathematical obligations.
11. Map ArkLib theorem coverage to the whole zkVM stack and state which end-to-end components remain
    outside ArkLib.

## Reporting Requirements

Each subagent report must name exact files and declarations touched, commands run, build or
validation status, axiom status where relevant, remaining assumptions, and blockers. Do not count a
wrapper as proof closure if it assumes the target theorem or the decisive witness.

## Suggested Workstreams

- Keystone integration: connect the existing `betaRec` bridge to section-5 data.
- Divisibility and recentering: discharge `Hlift H ∣ R` and gamma recentering obligations.
- Curve closure: replace `β_regular`, prove `hcoeffPoly`, and close
  `correlatedAgreement_affine_curves`.
- Validation repair: keep generated imports and KB artifacts current, and remove transient scratch
  files from the umbrella import path.
- Sorry audit: inventory proof-critical executable `sorry`s and classify their trust impact.
- ZKVM map: connect ArkLib theorems to claimed zkVM components and document remaining external
  verification work.
