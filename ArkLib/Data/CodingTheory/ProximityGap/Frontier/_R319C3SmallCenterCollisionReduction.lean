/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Tactic

/-!
# R319 (#466): small-center injectivity is a four-term relation exclusion

R318's seven-exception small-fiber slice has centers

```text
C(s,t) = ζ^s (ζ^t - 2ζ^k).
```

Its only unresolved global property is injectivity of this map on the chosen
parameter slice.  This file proves that two centers collide exactly when an
explicit four-term signed root relation vanishes.  It exposes the precise
arithmetic target for a resultant or sparse-relation argument, and records no
unproved nonvanishing as a theorem.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R319C3SmallCenterCollisionReduction

variable {F : Type*} [Field F]

/-- The center of the translated raw `c = 3` small-fiber collision. -/
def c3SmallCenter (ζ : F) (complement shift offset : ℕ) : F :=
  ζ ^ shift * (ζ ^ offset - (2 : F) * ζ ^ complement)

/-- The sparse four-term relation obtained by subtracting two small centers. -/
def c3SmallCenterCollision (ζ : F) (complement shift₁ offset₁ shift₂ offset₂ : ℕ) : F :=
  ζ ^ (shift₁ + offset₁) - ζ ^ (shift₂ + offset₂)
    - (2 : F) * ζ ^ (shift₁ + complement) + (2 : F) * ζ ^ (shift₂ + complement)

/-- Two raw small centers coincide exactly when their associated four-term
relation vanishes. -/
theorem c3SmallCenter_eq_iff_collision_zero
    (ζ : F) (complement shift₁ offset₁ shift₂ offset₂ : ℕ) :
    c3SmallCenter ζ complement shift₁ offset₁
      = c3SmallCenter ζ complement shift₂ offset₂
      ↔ c3SmallCenterCollision ζ complement shift₁ offset₁ shift₂ offset₂ = 0 := by
  unfold c3SmallCenter c3SmallCenterCollision
  rw [pow_add, pow_add, pow_add, pow_add]
  constructor <;> intro hrelation <;> linear_combination hrelation

/-- The exact named residual for the R318 small-fiber slice. -/
def C3SmallCenterInjective (ζ : F) (complement : ℕ)
    (parameters : Finset (ℕ × ℕ)) : Prop :=
  ∀ leftParameter ∈ parameters, ∀ rightParameter ∈ parameters,
    c3SmallCenter ζ complement leftParameter.1 leftParameter.2
        = c3SmallCenter ζ complement rightParameter.1 rightParameter.2
      → leftParameter = rightParameter

/-- Sparse four-term nonvanishing on a parameter set discharges the exact
small-center injectivity residual. -/
theorem c3SmallCenterInjective_of_collisionFree
    (ζ : F) (complement : ℕ) (parameters : Finset (ℕ × ℕ))
    (hcollision : ∀ leftParameter ∈ parameters, ∀ rightParameter ∈ parameters,
      leftParameter ≠ rightParameter →
        c3SmallCenterCollision ζ complement leftParameter.1 leftParameter.2
          rightParameter.1 rightParameter.2 ≠ 0) :
    C3SmallCenterInjective ζ complement parameters := by
  intro leftParameter hleft rightParameter hright hcenters
  by_contra hneq
  exact hcollision leftParameter hleft rightParameter hright hneq
    ((c3SmallCenter_eq_iff_collision_zero ζ complement leftParameter.1 leftParameter.2
      rightParameter.1 rightParameter.2).mp hcenters)

end ArkLib.ProximityGap.Frontier.R319C3SmallCenterCollisionReduction

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R319C3SmallCenterCollisionReduction.c3SmallCenter_eq_iff_collision_zero
#print axioms
  ArkLib.ProximityGap.Frontier.R319C3SmallCenterCollisionReduction.c3SmallCenterInjective_of_collisionFree
