/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAIncidenceCensus

/-!
# The closure family (#357 round 13): the fourth circuit-supply law

The exact char-0 census at `μ₁₆` (integer `ℤ[ζ₁₆]` sweep) is `1328 = 728 horizontal +
56 vertical + 288 slanted + 256` in a **fourth family** absent at `n = 8`: triples of
*non-antipodal* pairs from three *distinct* difference classes satisfying a signed
closure `±d₁ ± d₂ ± d₃ ≡ 0 (mod n/2)`, with positional congruences. (The mod-`97` count
`1712` contained `384` spurious `p`-coincidences — the integer sweep is the truth.)

This file lands the supply law of its principal matching type, **value-level** (domain-
agnostic): three disjoint pairs `P = {a,a'}, Q = {b,b'}, R = {c,c'}` whose invariants
satisfy the three **product relations**

`m_Q = −x_{a'}x_{c'}`, `m_R = −x_b x_{a'}`, `m_P = −x_b x_{c'}`

form a wide circuit: the collinearity determinant lies in the ideal of the relations
with the explicit certificate `D = (x_a − x_c)·R₁ + (x_{b'} − x_a)·R₂ + (x_c −
x_{b'})·R₃` (computer-verified symbolically, then checked by `linear_combination`).
Over `μ_n` the relations are exponent congruences (`b + b' ≡ a' + c' + n/2` etc.),
satisfiable in abundance — over generic domains, almost never: a fourth quantitative
expression of how smoothness creates the collision census.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-13 census comments); `MCADualPencilLaw.lean`,
  `MCAIncidenceCensus.lean`.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal

namespace ProximityGap.MCAClosureFamily

open ProximityGap.MCADualPencilLaw

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable (domain : ι ↪ F) {a a' b b' c c' : ι}

/-- **The closure-family supply law (principal type, value-level).** Three disjoint
pairs whose invariants satisfy the three product relations form a wide circuit. -/
theorem dependent_of_closure (h6 : Distinct6 a a' b b' c c')
    (hw1 : domain b * domain b' + domain a' * domain c' = 0)
    (hw2 : domain c * domain c' + domain b * domain a' = 0)
    (hw3 : domain a * domain a' + domain b * domain c' = 0) :
    ∃ α β γ : F, ¬(α = 0 ∧ β = 0 ∧ γ = 0) ∧
      ∀ i, α * dualVec domain {a, a', b, b'} i + β * dualVec domain {a, a', c, c'} i
        + γ * dualVec domain {b, b', c, c'} i = 0 := by
  rw [dependent_iff_collinear domain h6]
  linear_combination (domain a - domain c) * hw1 + (domain b' - domain a) * hw2
    + (domain c - domain b') * hw3

/-! ## Source audit -/

#print axioms dependent_of_closure

end ProximityGap.MCAClosureFamily
