/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.EntropyHammingBound
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The Hamming/sphere-packing bound in rate form

The rate form of the sphere-packing (Hamming) bound: a nonempty code with packing radius `⌊δn⌋`
satisfies `log_q |𝒞| ≤ log_q(n+1) + n·(1 − H_q(⌊δn⌋/n))`, i.e. rate `≤ 1 − H_q(δ) + o(1)`.  Obtained
by taking `log_q` of the entropy sphere-packing bound `card_le_qEntropy_of_minDist`.  Together with
the asymptotic Gilbert–Varshamov bound (`gv_existence_rate`, rate `≥ 1 − H_q(δ)`) and the rate
Singleton bound, this brackets the achievable rate–distance region.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodingTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F]

/-- **Rate-form Hamming/sphere-packing bound.** A nonempty code with packing radius `⌊δn⌋` (pairwise
distance `≥ 2⌊δn⌋+1`) over `q ≥ 2` satisfies `log_q|𝒞| ≤ log_q(n+1) + n·(1 − H_q(⌊δn⌋/n))` — the
sphere-packing rate bound, companion to the asymptotic GV bound. -/
theorem hamming_logb_le (hq : 2 ≤ Fintype.card F) (C : Finset (ι → F)) (δ : ℝ)
    (hk0 : 0 < ⌊δ * Fintype.card ι⌋₊) (hkn : ⌊δ * Fintype.card ι⌋₊ < Fintype.card ι)
    (hpack : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → 2 * ⌊δ * Fintype.card ι⌋₊ + 1 ≤ hammingDist c c')
    (hne : C.Nonempty) :
    Real.logb (Fintype.card F) (C.card : ℝ)
      ≤ Real.logb (Fintype.card F) ((Fintype.card ι : ℝ) + 1)
        + (Fintype.card ι : ℝ)
          * (1 - qEntropy (Fintype.card F)
              ((⌊δ * Fintype.card ι⌋₊ : ℝ) / (Fintype.card ι : ℝ))) := by
  have hqr : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hpos : (0 : ℝ) < (C.card : ℝ) := by exact_mod_cast hne.card_pos
  have hcard := card_le_qEntropy_of_minDist hq C δ hk0 hkn hpack
  calc Real.logb (Fintype.card F) (C.card : ℝ)
      ≤ Real.logb (Fintype.card F)
          (((Fintype.card ι : ℝ) + 1)
            * (Fintype.card F : ℝ)
              ^ ((Fintype.card ι : ℝ)
                  * (1 - qEntropy (Fintype.card F)
                      ((⌊δ * Fintype.card ι⌋₊ : ℝ) / (Fintype.card ι : ℝ))))) :=
        Real.logb_le_logb_of_le hqr hpos hcard
    _ = Real.logb (Fintype.card F) ((Fintype.card ι : ℝ) + 1)
        + Real.logb (Fintype.card F)
            ((Fintype.card F : ℝ)
              ^ ((Fintype.card ι : ℝ)
                  * (1 - qEntropy (Fintype.card F)
                      ((⌊δ * Fintype.card ι⌋₊ : ℝ) / (Fintype.card ι : ℝ))))) :=
        Real.logb_mul (by positivity) (by positivity)
    _ = Real.logb (Fintype.card F) ((Fintype.card ι : ℝ) + 1)
        + (Fintype.card ι : ℝ)
          * (1 - qEntropy (Fintype.card F)
              ((⌊δ * Fintype.card ι⌋₊ : ℝ) / (Fintype.card ι : ℝ))) := by
        rw [Real.logb_rpow (by positivity) (by exact_mod_cast (by omega : Fintype.card F ≠ 1))]

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.hamming_logb_le
