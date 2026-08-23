/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MobiusPencilEnergy
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Even support of the Möbius involution (#389)

The Möbius pencil involution `σ_b : Equiv.Perm G` (`x ↦ b·x⁻¹`) satisfies `σ_b² = 1`
(`mobiusInvol_sq`); hence its support (the non-fixed points) has **even** cardinality, via Mathlib's
`Equiv.Perm.two_dvd_card_support`.  The fixed points are the square roots of `b`, so this counts the
non-square-root elements in pairs — the next structural brick flagged in `MobiusPencilEnergy`.
-/

set_option linter.unusedSectionVars false


namespace ProximityGap.MobiusPencil

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- **Even support of the Möbius involution.** Since `σ_b² = 1`, its support (the non-fixed points,
i.e. the elements that are not square roots of `b`) has even cardinality. -/
theorem support_card_even (b : G) : Even (mobiusInvol b).support.card := by
  have hsq : (mobiusInvol b) ^ 2 = 1 := by rw [pow_two]; exact mobiusInvol_sq b
  obtain ⟨c, hc⟩ := Equiv.Perm.two_dvd_card_support hsq
  exact ⟨c, by omega⟩

end ProximityGap.MobiusPencil
