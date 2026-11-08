/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Coefficient-dependent batching outputs

The retired Batched FRI tail carried batching coefficients in its non-oracle input statement.
A canonical output representation can observe input oracles, transcript messages and challenges,
but not that statement. Even one coefficient prevents such a statement-independent representation
of the initial combined oracle. The canonical batching round solves this by exposing the combined
oracle before the FRI tail begins.
-/
namespace ProximityPrize.Compatibility.BatchedFri

/-- A statement-independent output cannot implement even the two-coordinate batching family. -/
theorem no_statement_independent_batching_output (F : Type) [Semiring F] [Nontrivial F] :
    ¬ ∃ output : (Fin 2 → F) → F,
      ∀ coefficient : F, ∀ inputs : Fin 2 → F,
        output inputs = inputs 0 + coefficient * inputs 1 := by
  rintro ⟨output, h⟩
  have hzero := h 0 ![0, 1]
  have hone := h 1 ![0, 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    zero_mul, zero_add, one_mul] at hzero hone
  exact zero_ne_one (hzero.symm.trans hone)

#print axioms no_statement_independent_batching_output
end ProximityPrize.Compatibility.BatchedFri
