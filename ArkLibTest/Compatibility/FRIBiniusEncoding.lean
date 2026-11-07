/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Basic

/-! The two input coefficient conventions already differ before any folding or challenge. -/
namespace ArkLibTest.Compatibility.FRIBiniusEncoding
open Binius.BinaryBasefold

theorem chronological_coefficient_bit :
    bitsOfIndex (L := ℚ) (n := 2) (1 : Fin 4) (0 : Fin 2) = 1 := by decide

theorem historical_coefficient_bit :
    statementOrderBitsOfIndex (L := ℚ) (n := 2) (1 : Fin 4) (0 : Fin 2) = 0 := by decide

theorem input_coefficient_views_differ :
    statementOrderBitsOfIndex (L := ℚ) (n := 2) (1 : Fin 4) ≠
      bitsOfIndex (L := ℚ) (n := 2) (1 : Fin 4) := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  rw [historical_coefficient_bit, chronological_coefficient_bit] at h0
  exact zero_ne_one h0

#print axioms chronological_coefficient_bit
#print axioms historical_coefficient_bit
#print axioms input_coefficient_views_differ
end ArkLibTest.Compatibility.FRIBiniusEncoding
