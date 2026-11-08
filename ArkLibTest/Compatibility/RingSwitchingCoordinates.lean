/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Algebra
import ArkLib.Data.MvPolynomial.RestrictDegree
import Mathlib.Data.ZMod.Basic

/-!
# Canonical ring-switching conventions

These clients distinguish prefix fixing from the retired suffix convention, and check which
tensor coordinate family recovers the packed right factor. See the integration migration audit.
-/

namespace ArkLibTest.Compatibility.RingSwitchingCoordinates

open MvPolynomial

/-- Fixing the first variable to `2` leaves `2 + 3X`, whose value at `1` is `5`. -/
theorem prefix_evaluation : MvPolynomial.eval (fun _ : Fin 1 => (1 : ZMod 7))
    (MvPolynomial.fixFirstVariablesOfMQP 2 ⟨1, by decide⟩
      (X 0 + C 3 * X 1 : MvPolynomial (Fin 2) (ZMod 7)) (fun _ => 2)) = 5 := by
  have h := MvPolynomial.eval_fixFirstVariablesOfMQP (L := ZMod 7) (ℓ := 2)
    (⟨1, by decide⟩ : Fin 3) (X 0 + C 3 * X 1) (fun _ => 2) (fun _ => 1)
  norm_num at h
  exact h

/-- The canonical columns recover the right tensor factor's basis coordinates. -/
theorem packed_factor_coordinates (κ : ℕ) (K L : Type)
    [CommRing K] [CommRing L] [Algebra K L]
    (β : Module.Basis (Fin κ → Fin 2) K L) (a b : L) :
    (RingSwitching.tensorProductProfile κ K L β).decomposeColumns
      (RingSwitching.φ₀ L K a * RingSwitching.φ₁ L K b) =
      fun u => β.repr b u • a := by
  simpa only [Algebra.smul_def] using
    (RingSwitching.tensorProductProfile κ K L β).decomposeColumns_φ₀_mul_φ₁ a b

end ArkLibTest.Compatibility.RingSwitchingCoordinates

#print axioms ArkLibTest.Compatibility.RingSwitchingCoordinates.prefix_evaluation
#print axioms ArkLibTest.Compatibility.RingSwitchingCoordinates.packed_factor_coordinates
