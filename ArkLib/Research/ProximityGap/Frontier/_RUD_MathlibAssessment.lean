/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.Combinatorics.Additive.RudnevIncidence

/-!
# Rudnev incidence leg: dated Mathlib implementation inventory

This file records the result of a **textual search** (dated 2026-06, against the Mathlib then
vendored under `.lake/packages/mathlib`) for primitives that could help discharge
`Rudnev.RudnevIncidenceCore`, the algebraic-geometric core of the point–plane incidence bound (see
`ArkLib/ToMathlib/Combinatorics/Additive/RudnevIncidence.lean`). It is an implementation
inventory, not a proof that every elementary or Mathlib route is exhausted.

## Correction (audits L57 / R-137)

An earlier version of this file asserted an `IRREDUCIBLE-AG-CEILING` verdict for a core predicate
`I ≤ m·n/q + √(m·n·q) + n` under only `m ≤ n ≤ q·m`, describing it as Rudnev's established theorem
awaiting Klein-quadric machinery. That predicate was **false** (five collinear points and six
normalized planes through their line over `F₅` give `30 > 12 + √150` incidences); it is now named
`Rudnev.NaiveIncidenceBound` and refuted by `Rudnev.not_naiveIncidenceBound_zmod5`. The library
core `Rudnev.RudnevIncidenceCore C c₀ F` was repaired to Rudnev's actual statement
([arXiv:1407.0426](https://arxiv.org/abs/1407.0426), Theorem 3): `I ≤ C·(m·√n + m·k)` for `n ≤ m`
normalized planes, `k` the maximum number of collinear planes, `char F ≠ 2` and `n ≤ c₀·p²`, with
the constants fixed uniformly by `Rudnev.RudnevIncidenceTheorem`. The inventory below refers to that
repaired target.

## Inventory (dated, textual)

Rudnev's saving is proved via the **Klein-quadric** lifting of lines in `F³` to points of a quadric
`Q ⊂ P⁵`, followed by a point–line incidence count on `Q`. At the time of the search the following
were not found in Mathlib:

| Needed primitive | Mathlib status (2026-06 search) |
|---|---|
| Klein quadric / Plücker embedding | not found (no `Plücker`/`plucker`) |
| Szemerédi–Trotter / point–line or point–plane incidence bound | not found |
| Polynomial partitioning / Guth–Katz | not found |
| Grassmannian as a flag-counting combinatorial object | not found (`RingTheory.Grassmannian` is the scheme-theoretic structure) |

On-topic primitives that were found: `sq_sum_le_card_mul_sum_sq` (used by `Rudnev.sq_incidences_le`)
and Alon's Combinatorial Nullstellensatz (`MvPolynomial.combinatorial_nullstellensatz_*`), which is
not by itself the tool Rudnev's argument uses. This is an assessment of effort, not a theorem:
discharging the repaired core natively is a substantial formalization project.

## What this file contributes (axiom-clean)

Two re-exports: `rudnevCore_conditional`, the conditional bound from the repaired core (a direct
application of `Rudnev.incidence_bound`; it certifies nothing about irreducibility), and
`elementary_scaffold_stops_at_second_moment`, the proven Cauchy–Schwarz reduction.
-/

open Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.RUD

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Conditional bound from the repaired core (PROVEN, axiom-clean).** A direct application of
`Rudnev.incidence_bound`: assuming `Rudnev.RudnevIncidenceCore C c₀ F`, Rudnev's hypotheses give
`I(P, Pl) ≤ C · (#P·√#Pl + #P·k)`. This is a wiring check only; it does not show that the core is
irreducible. -/
theorem rudnevCore_conditional {C c₀ : ℝ} (h : Rudnev.RudnevIncidenceCore C c₀ F)
    (hchar : ringChar F ≠ 2)
    (P : Finset (Rudnev.Point F)) (Pl : Finset (Rudnev.Plane F))
    (hPl : ∀ π ∈ Pl, Rudnev.IsNormalizedPlane π)
    (hnm : #Pl ≤ #P) (hp : (#Pl : ℝ) ≤ c₀ * (ringChar F : ℝ) ^ 2) :
    (Rudnev.incidences P Pl : ℝ)
      ≤ C * ((#P : ℝ) * Real.sqrt (#Pl : ℝ)
        + (#P : ℝ) * (Rudnev.maxCollinearPlanes Pl : ℝ)) :=
  Rudnev.incidence_bound h hchar P Pl hPl hnm hp

/-- **The elementary Cauchy–Schwarz reduction (PROVEN, axiom-clean).** Re-export of
`Rudnev.sq_incidences_le`: incidences are controlled by the second moment `∑_x deg(x)²`. -/
theorem elementary_scaffold_stops_at_second_moment
    (P : Finset (Rudnev.Point F)) (Pl : Finset (Rudnev.Plane F)) :
    (Rudnev.incidences P Pl : ℝ) ^ 2
      ≤ (#P : ℝ) * ∑ x ∈ P, ((Rudnev.pointDeg Pl x : ℝ)) ^ 2 :=
  Rudnev.sq_incidences_le P Pl

end ArkLib.ProximityGap.RUD

-- Axiom audit (expected: propext, Classical.choice, Quot.sound)
#print axioms ArkLib.ProximityGap.RUD.rudnevCore_conditional
#print axioms ArkLib.ProximityGap.RUD.elementary_scaffold_stops_at_second_moment
