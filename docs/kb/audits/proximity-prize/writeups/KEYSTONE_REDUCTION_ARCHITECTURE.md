# Keystone reduction architecture

## Overview

The BCIKS20 Section 5 keystone is best treated as a reduction architecture rather than a monolithic
proof obligation. The current ArkLib work decomposes the route into small verified bricks plus a few
honest residual hypotheses that correspond to external or still-open mathematical content.

## Main objects

### Ingredient-D DAG

The ingredient-D route is a 28-brick dependency graph for the Hensel and coefficient-polynomial
machinery. Its purpose is to keep algebraic infrastructure separate from the list-decoding
front-door theorem.

### BetaCurveInputFin

`BetaCurveInputFin`-shaped data packages the finite inputs needed to pass from the beta recursion and
curve data into coefficient-polynomial witnesses. The design intent is that the bundle records
inputs and side conditions, not the final per-coefficient conclusion.

That intent was not met by the original field list. Its specialisation field `hPz` was quantified
over *every* decoded family `P : F → F[X]`, while the bundle's own representative fields
(`hrep`/`hdegX`) satisfy the premise of `hPz`; instantiating it at `P := 0` and `P := 1` forces
`0 = 1` at any good parameter. So the bundle, and its siblings `BetaCurveInput`,
`BetaCurveInputOffcentre` and `BetaCurveInputOffcentreFin`, was empty whenever the good-coefficient
set is nonempty (audit L72; this is a false interface, not a Lean inconsistency or a statement
about BCIKS20). The bundles now take `P` as a parameter and `hPz` speaks about that family only;
the checked regressions are `BetaCurveInput*.not_uniform_hPz` in
`ArkLib/ToMathlib/KeystoneStrictResidual.lean`. No inhabitant has been constructed in any regime,
and the bundles carry further independent obstructions listed in that file's module docstring.

### Residual-ladder compression

Instead of carrying anonymous proof holes, the formalization compresses the remaining BCIKS20
Section 5 debt into named residual APIs. Each reduction theorem should say: given this precise
residual input, the downstream theorem follows.

## Why this architecture matters

This structure gives future work three useful properties:

* Locality: algebraic bricks can be audited independently.
* Honesty: external theorem debt is visible in theorem statements or named residual definitions.
* Reuse: downstream FRI/STIR/WHIR work can depend on narrowed reductions without pretending the
  keystone is fully closed.

## Current guidance

Use `docs/kb/audits/proximity-prize/CURRENT-RESIDUALIZED-TREE-2026-06-06.md` and the focused GitHub
issues as the current work index. Older campaign ledgers are provenance, not current source of
truth.
