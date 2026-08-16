/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import ArkLib.Data.CodingTheory.JohnsonBound.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.InformationTheory.Hamming
import ArkLib.Data.CodingTheory.ProximityGap.MCAGS

open scoped NNReal

namespace ArkLib.JohnsonBound
def johnsonDenomInt (n d e : ℕ) : ℤ := (d : ℤ) * n - 2 * e * n
end ArkLib.JohnsonBound

def hwitAll_common_center_false_above_half_johnson : Prop :=
    ∃ (ι F : Type) (_ : Fintype ι) (_ : Nonempty ι) (_ : DecidableEq ι)
      (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (k : ℕ) (_ : NeZero k)
      (domain : ι ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) ι),
      ((1 - Real.sqrt ((k:ℝ)/Fintype.card ι))/2 < (δ:ℝ)) ∧
      ((δ:ℝ) < 1 - Real.sqrt ((k:ℝ)/Fintype.card ι)) ∧
      ¬ (∃ x : ι, u 1 x ≠ 0 ∧ ∃ w : ι → F, ∃ e : ℕ,
          0 < ArkLib.JohnsonBound.johnsonDenomInt
            (Fintype.card ι) (Fintype.card ι - k + 1) e ∧
          ∀ γ : F, δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ →
            ∃ c ∈ (ReedSolomon.code domain k : Set (ι → F)),
              Δ₀(c, w) ≤ e ∧ c x = u 0 x + γ * u 1 x)
