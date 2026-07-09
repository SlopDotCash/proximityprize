> Filed from a 2026-06-09 end-to-end gap audit. Git archaeology across all 1230 refs confirms this is **genuinely open / never proven** (not a lost proof — the 7bbce943f wipe was fully recovered). Its predecessor tracking issue was closed with the core left open.

## BCIKS20 correlated-agreement open cores: `StrictCoeffPolysResidual` / `BoundaryCardResidual`

**Current state** (`ArkLib/Data/CodingTheory/ProximityGap/`): the correlated-agreement theorems are in **proved-modulo-residual** form — e.g. `RS_correlatedAgreement_affineLines` and `correlatedAgreement_affine_curves_of_*` are closed theorems that **consume** two explicit `Prop` hypotheses:
- `StrictCoeffPolysResidual` — [BCIKS20] §5 strict Johnson-branch coefficient-polynomial extraction.
- `BoundaryCardResidual` — [BCIKS20] §6.2 closed square-root boundary assembly.

These are the genuine open obligations gating STIR/WHIR/FRI soundness in the Johnson regime. They are **known mathematics** ([BCIKS20] Proximity Gaps, FOCS'20) but not yet discharged in-tree.

**Why this issue:** the predecessors #7/#8 were CLOSED with the explicit note "remaining proof work is unchanged" — i.e. the cores were left open and the tracking lost. This re-opens dedicated tracking. This is **distinct from #232** (the prize is pinning `δ*` in the Johnson→capacity interior; this is the *known* Johnson-radius CA that the deployed protocols need).

Predecessors (CLOSED, cores left open): #7, #8.
