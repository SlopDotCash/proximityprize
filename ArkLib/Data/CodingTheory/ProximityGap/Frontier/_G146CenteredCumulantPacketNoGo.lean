/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
# G146: center-first partition cumulants are not positive packet counts

The uncentered Möbius--Mann packet route was killed by the DC term: ordinary partition
cumulants amplify the uniform finite-field main term instead of isolating primitive packets.  A
natural repair is to subtract the uniform main term first and then apply the same connected
partition recurrence.  This file records the smallest formal obstruction to that repair.

For moments `M₁, …, M₄`, the ordinary distinguished-block moment/cumulant recurrence is

```text
K₁ = M₁
K₂ = M₂ - K₁ M₁
K₃ = M₃ - K₁ M₂ - 2 K₂ M₁
K₄ = M₄ - K₁ M₃ - 3 K₂ M₂ - 3 K₃ M₁.
```

The exact `μ₈ ⊂ F₄₁` centered zero-sum moments through depth four are

```text
Mᶜ₁ = -8/41,    Mᶜ₂ = 264/41,    Mᶜ₃ = -512/41,    Mᶜ₄ = 4104/41,
```

coming from raw counts `M₁=0, M₂=8, M₃=0, M₄=200` after subtracting `8^m/41`.
The resulting connected coefficient is

```text
Kᶜ₄ = -87878392 / 2825761 < 0.
```

So the center-first partition recurrence still produces signed Ursell/fluctuation weights, not a
literal nonnegative packet census.  Any surviving packet calculus must introduce a new positive
canonical minimal-zero-sum packetization; it cannot reuse ordinary partition cumulants after
centering.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G146CenteredCumulantPacketNoGo

/-- Centered finite-field moment from a raw ordered zero-sum count: `count - n^m/q`. -/
def centeredMoment (count n q m : ℕ) : ℚ :=
  (count : ℚ) - (n : ℚ) ^ m / (q : ℚ)

/-- First connected coefficient in the ordinary partition moment-cumulant recurrence. -/
def connectedK1 (M1 : ℚ) : ℚ := M1

/-- Second connected coefficient in the ordinary partition moment-cumulant recurrence. -/
def connectedK2 (M1 M2 : ℚ) : ℚ :=
  M2 - connectedK1 M1 * M1

/-- Third connected coefficient in the ordinary partition moment-cumulant recurrence. -/
def connectedK3 (M1 M2 M3 : ℚ) : ℚ :=
  M3 - connectedK1 M1 * M2 - 2 * connectedK2 M1 M2 * M1

/-- Fourth connected coefficient in the ordinary partition moment-cumulant recurrence. -/
def connectedK4 (M1 M2 M3 M4 : ℚ) : ℚ :=
  M4 - connectedK1 M1 * M3 - 3 * connectedK2 M1 M2 * M2
    - 3 * connectedK3 M1 M2 M3 * M1

/-- The centered depth-one moment of the exact `μ₈ ⊂ F₄₁` cell. -/
theorem mu8_F41_centeredMoment1 : centeredMoment 0 8 41 1 = -8 / 41 := by
  norm_num [centeredMoment]

/-- The centered depth-two moment of the exact `μ₈ ⊂ F₄₁` cell. -/
theorem mu8_F41_centeredMoment2 : centeredMoment 8 8 41 2 = 264 / 41 := by
  norm_num [centeredMoment]

/-- The centered depth-three moment of the exact `μ₈ ⊂ F₄₁` cell. -/
theorem mu8_F41_centeredMoment3 : centeredMoment 0 8 41 3 = -512 / 41 := by
  norm_num [centeredMoment]

/-- The centered depth-four moment of the exact `μ₈ ⊂ F₄₁` cell. -/
theorem mu8_F41_centeredMoment4 : centeredMoment 200 8 41 4 = 4104 / 41 := by
  norm_num [centeredMoment]

/-- Exact value of the center-first fourth partition-connected coefficient for `μ₈ ⊂ F₄₁`.
The negative sign is the route-closing obstruction: this coefficient cannot be a cardinality of
literal packets. -/
theorem mu8_F41_centered_connectedK4_value :
    connectedK4 (centeredMoment 0 8 41 1) (centeredMoment 8 8 41 2)
      (centeredMoment 0 8 41 3) (centeredMoment 200 8 41 4)
      = -87878392 / 2825761 := by
  norm_num [connectedK4, connectedK3, connectedK2, connectedK1, centeredMoment]

/-- **Centered partition-cumulant no-go.**  In the exact `μ₈ ⊂ F₄₁` cell, after subtracting
the uniform main term first, the ordinary fourth connected coefficient is strictly negative.
Thus ordinary center-first partition connectedness is a signed fluctuation transform, not a
nonnegative packet-counting invariant. -/
theorem mu8_F41_centered_connectedK4_negative :
    connectedK4 (centeredMoment 0 8 41 1) (centeredMoment 8 8 41 2)
      (centeredMoment 0 8 41 3) (centeredMoment 200 8 41 4) < 0 := by
  norm_num [connectedK4, connectedK3, connectedK2, connectedK1, centeredMoment]

/-- There is no universal nonnegativity theorem for fourth ordinary partition-connected
coefficients after centering.  The displayed finite-field cell above is already a countermodel to
that shape. -/
theorem not_forall_centered_connectedK4_nonnegative :
    ¬ (∀ M1 M2 M3 M4 : ℚ, 0 ≤ connectedK4 M1 M2 M3 M4) := by
  intro h
  have hnonneg := h (centeredMoment 0 8 41 1) (centeredMoment 8 8 41 2)
    (centeredMoment 0 8 41 3) (centeredMoment 200 8 41 4)
  exact (not_le_of_gt mu8_F41_centered_connectedK4_negative) hnonneg

end ArkLib.ProximityGap.Frontier.G146CenteredCumulantPacketNoGo

/-! ## Axiom audit -/
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.G146CenteredCumulantPacketNoGo.mu8_F41_centered_connectedK4_value
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.G146CenteredCumulantPacketNoGo.mu8_F41_centered_connectedK4_negative
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.G146CenteredCumulantPacketNoGo.not_forall_centered_connectedK4_nonnegative
