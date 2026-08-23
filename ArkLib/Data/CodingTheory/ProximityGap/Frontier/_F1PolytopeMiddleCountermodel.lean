/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ50WitnessRealizability
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ59EmptyMiddle

/-!
# F1 polytope realizability does not exclude the middle band

The F1 residual asks for exclusion of `SYZ59.middleBand` on genuinely realizable witness
polynomials.  The existing predicate `SYZ50.Realizable` records only the rate-`1/2` Venn-region,
budget, and interior-slack inequalities.  It does not mention a field, evaluation domain,
polynomials, a syzygy, or its minimal product-degree.

This file gives an infinite arithmetic countermodel family to the tempting statement

`SYZ50.Realizable a b c t k → ¬ SYZ59.middleBand a b c δ₁`.

For every `d ≥ 6`, the balanced profile

* `(a,b,c) = (d,d,d)`,
* `t = d - 2`,
* `k = 2d - 1`, and
* candidate minimal product-degree `δ₁ = d + 1`

satisfies both predicates.  Therefore the open F1 exclusion cannot be formulated from
`SYZ50.Realizable` alone: it needs a stronger predicate binding the numeric profile to actual
band witness polynomials and the minimal generator degree of their syzygy module.

This is a statement-interface refutation only.  It does not construct such witness polynomials,
refute the genuine empty-middle conjecture, or advance the Paley/BGK analytic wall.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.F1PolytopeMiddleCountermodel

/-- Every balanced profile in the family satisfies the arithmetic rate-`1/2` realizability
polytope.  At the chosen parameters, domain disjointness and the budget cap are tight. -/
theorem realizable_family (d : ℕ) (hd : 6 ≤ d) :
    SYZ50.Realizable d d d (d - 2) (2 * d - 1) := by
  unfold SYZ50.Realizable
  omega

/-- The same family carries a numeric middle-band candidate at `δ₁ = d + 1`.  The lower edge is
strictly above the floor `d`, while `d ≥ 6` puts it below `⌊3d/2⌋ - 2`. -/
theorem middleBand_family (d : ℕ) (hd : 6 ≤ d) :
    SYZ59.middleBand d d d (d + 1) := by
  unfold SYZ59.middleBand
  omega

/-- **Infinite-family countermodel.**  Numeric band realizability and membership in the middle band
are jointly satisfiable for every `d ≥ 6`. -/
theorem realizable_and_middleBand_family (d : ℕ) (hd : 6 ≤ d) :
    SYZ50.Realizable d d d (d - 2) (2 * d - 1) ∧
      SYZ59.middleBand d d d (d + 1) :=
  ⟨realizable_family d hd, middleBand_family d hd⟩

/-- The universal implication from the current polytope predicate to empty-middle is false.  The
smallest member of the family is `(d,t,k,δ₁) = (6,4,11,7)`. -/
theorem not_realizable_implies_no_middleBand :
    ¬ (∀ a b c t k δ₁ : ℕ,
      SYZ50.Realizable a b c t k → ¬ SYZ59.middleBand a b c δ₁) := by
  intro h
  exact h 6 6 6 4 11 7 (realizable_family 6 (by decide))
    (middleBand_family 6 (by decide))

end ArkLib.ProximityGap.F1PolytopeMiddleCountermodel

-- Honesty audit:
#print axioms ArkLib.ProximityGap.F1PolytopeMiddleCountermodel.realizable_family
#print axioms ArkLib.ProximityGap.F1PolytopeMiddleCountermodel.middleBand_family
#print axioms ArkLib.ProximityGap.F1PolytopeMiddleCountermodel.realizable_and_middleBand_family
#print axioms ArkLib.ProximityGap.F1PolytopeMiddleCountermodel.not_realizable_implies_no_middleBand
