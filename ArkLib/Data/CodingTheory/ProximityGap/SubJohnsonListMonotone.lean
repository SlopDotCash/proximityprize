/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonListSupply

/-!
# Monotonicity of the sub-Johnson list bound (#389)

The named-open residual `SubJohnsonListBound dom k m L A` (the recognized explicit-RS-beyond-Johnson
list-size problem) is monotone in both numeric budgets: weakening `L → L'` and `A → A'` preserves it.
This lets downstream consumers quote a loose upper bracket `(L', A')` without re-proving tightness of
the witnessed `(L, A)`.  It loosens the budget only — it does **not** discharge the open core.
-/

set_option linter.unusedSectionVars false


open Finset

namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **Monotonicity of the sub-Johnson list bound in both numeric budgets.**  If
`SubJohnsonListBound dom k m L A` holds, then it holds for every larger `L' ≥ L`, `A' ≥ A`. -/
theorem subJohnsonListBound_mono {dom : Fin n ↪ F} {k m L A L' A' : ℕ}
    (hL : L ≤ L') (hA : A ≤ A') (h : SubJohnsonListBound dom k m L A) :
    SubJohnsonListBound dom k m L' A' := by
  intro w
  obtain ⟨hLcard, hAcard⟩ := h w
  exact ⟨Nat.le_trans hLcard hL, fun c hc => Nat.le_trans (hAcard c hc) hA⟩

end ProximityGap.Ownership
