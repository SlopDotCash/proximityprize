/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Matrix.Basic

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova
-/

import Mathlib.LinearAlgebra.Matrix.Hadamard
import ArkLib.Data.Fin.Tuple.Defs
import ProximityPrize.Extensions.Data.MvPolynomial.Multilinear

/-!
  # Auxiliary definitions and lemmas for matrices
-/

namespace Matrix

variable {α : Type*}
         {F : Type} [Field F]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ'] [DecidableEq ℓ']

end Matrix

namespace Matrix

open MvPolynomial

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- Evaluating `toMLE` at Boolean row and column points recovers the corresponding matrix entry. -/
theorem toMLE_eval_boolPoint
    (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (xBits : Fin m → Fin 2) (yBits : Fin n → Fin 2) :
    MvPolynomial.eval (yBits : Fin n → R)
        (MvPolynomial.eval ((MvPolynomial.C ∘ (xBits : Fin m → R)) :
          Fin m → MvPolynomial (Fin n) R) M.toMLE)
      = M (finFunctionFinEquiv xBits) (finFunctionFinEquiv yBits) := by
  change MvPolynomial.eval (yBits : Fin n → R)
      (MvPolynomial.eval (MvPolynomial.C ∘ (xBits : Fin m → R))
        (MvPolynomial.MLE' (fun row => MvPolynomial.MLE' (fun col => M row col)))) = _
  have hx :
      ((MvPolynomial.C ∘ (xBits : Fin m → R)) :
          Fin m → MvPolynomial (Fin n) R) =
        (xBits : Fin m → MvPolynomial (Fin n) R) := by
    funext i
    simp
  rw [hx, MvPolynomial.MLE'_eval_zeroOne]
  simp

#print axioms Matrix.toMLE_eval_boolPoint

end Matrix
