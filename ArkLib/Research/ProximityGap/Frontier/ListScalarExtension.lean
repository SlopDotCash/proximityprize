/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds

/-! # Scalar Reed–Solomon list sizes under field extension -/

namespace ProximityGap.ListScalarExtension

/-- Extending the evaluation domain along a field embedding preserves every scalar
list witness, at the same radius and degree bound. -/
theorem lambda_le {I F E : Type*} [Fintype I] [Field F] [Field E]
    (f : F →+* E) (D : I ↪ F) (k : ℕ) (δ : ℝ) :
    Code.Lambda (ReedSolomon.code D k : Set (I → F)) δ ≤
      Code.Lambda (ReedSolomon.code (D.trans ⟨f, f.injective⟩) k : Set (I → E)) δ :=
  Code.Lambda_le_of_injective_comp f.injective
    (fun _ hc ↦ ReedSolomon.comp_mem_code_map D f f.injective hc) δ

end ProximityGap.ListScalarExtension

#print axioms ProximityGap.ListScalarExtension.lambda_le
