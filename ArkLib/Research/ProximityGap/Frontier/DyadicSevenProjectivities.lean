/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicSevenField
import ArkLib.Research.ProximityGap.Frontier.DyadicFiveConicMatches

/-! # Seven matched dyadic roots force a scaling or reciprocal scaling -/

namespace ProximityGap.DyadicSevenProjectivities
open DyadicSevenDescent DyadicSevenField
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

private theorem conics {j : ℕ} (pos : 0<j) {z : K} (root : IsPrimitiveRoot z (2^(j+1))) :
    NoFive z := by
  let E := IntermediateField.adjoin ℚ ({z}:Set K)
  let w : E := ⟨z,IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩
  let φ : E →+* K := E.subtype
  have prim : IsPrimitiveRoot w (2^(j+1)) :=
    (show IsPrimitiveRoot (φ w) (2^(j+1)) from root).of_map_of_injective φ.injective
  let _ : Algebra ℚ E := E.algebra'
  let _ : IsCyclotomicExtension {2^(j+1)} ℚ E :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin (2^(j+1)) ℚ K E root).2 rfl
  exact conic_lift φ (w:=w) rfl (DyadicExceptionalConic.five pos prim)

/-- In any characteristic-zero field, a nonsingular projective map carrying
seven distinct roots of order dividing a power of two to seven such roots
is a scaling or a reciprocal scaling. This includes arbitrary complex
coefficients and every power-of-two grid size. -/
theorem all_orders {m : ℕ} {z : K} (root : IsPrimitiveRoot z (2^m)) : Rigid z := by
  let E := IntermediateField.adjoin ℚ ({z}:Set K)
  let w : E := ⟨z,IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩
  let φ : E →+* K := E.subtype
  have prim : IsPrimitiveRoot w (2^m) :=
    (show IsPrimitiveRoot (φ w) (2^m) from root).of_map_of_injective φ.injective
  let _ : Algebra ℚ E := E.algebra'
  let _ : IsCyclotomicExtension {2^m} ℚ E :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin (2^m) ℚ K E root).2 rfl
  let _ := IsCyclotomicExtension.isGalois {2^m} ℚ E
  exact rigid_lift φ (w:=w) rfl (normal_orders (fun _ pos _ hz => conics pos hz) prim)

end ProximityGap.DyadicSevenProjectivities
#print axioms ProximityGap.DyadicSevenProjectivities.all_orders
