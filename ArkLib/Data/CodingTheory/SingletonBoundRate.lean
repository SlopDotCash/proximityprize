/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.SingletonBound
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The Singleton bound in rate form

The standard rate/dimension form of the Singleton bound: a nonempty code with minimum distance `≥ d`
over a field with `q ≥ 2` satisfies

  `log_q |𝒞| ≤ n − (d−1)`,

i.e. its dimension (rate × n) is at most `n − d + 1` — the rate–distance tradeoff `R ≤ 1 − δ + 1/n`.
Obtained by taking `log_q` of the cardinality Singleton bound `|𝒞| ≤ q^{n−(d−1)}`.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F]

/-- **Rate-form Singleton bound.**  For a nonempty code with minimum distance `≥ d` over a field with
`q ≥ 2`, `log_q |𝒞| ≤ n − (d−1)`. -/
theorem singleton_logb_le (𝒞 : Finset (ι → F)) (d : ℕ) (hd : 1 ≤ d) (hq : 2 ≤ Fintype.card F)
    (hne : 𝒞.Nonempty)
    (hmin : ∀ c ∈ 𝒞, ∀ c' ∈ 𝒞, c ≠ c' → d ≤ hammingDist c c') :
    Real.logb (Fintype.card F) (𝒞.card : ℝ) ≤ (Fintype.card ι - (d - 1) : ℕ) := by
  have hqr : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hpos : (0 : ℝ) < (𝒞.card : ℝ) := by exact_mod_cast hne.card_pos
  have hcardr : (𝒞.card : ℝ) ≤ (Fintype.card F : ℝ) ^ (Fintype.card ι - (d - 1)) := by
    exact_mod_cast singleton_bound 𝒞 d hd hmin
  calc Real.logb (Fintype.card F) (𝒞.card : ℝ)
      ≤ Real.logb (Fintype.card F) ((Fintype.card F : ℝ) ^ (Fintype.card ι - (d - 1))) :=
        Real.logb_le_logb_of_le hqr hpos hcardr
    _ = (Fintype.card ι - (d - 1) : ℕ) := by
        rw [Real.logb_pow, Real.logb_self_eq_one hqr, mul_one]

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.singleton_logb_le
