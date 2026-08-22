/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26PolyFieldCeiling
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZamanConstructor

/-!
# B3 — A FULLY CONCRETE, MACHINE-CHECKED KKH26 δ* CEILING (#334)

The whole B3 (s=128) machine, exercised end-to-end on an *explicit* code with **no analytic number
theory**.  `KKH26ThornerZamanConstructor.tzPrimeSupply_of_subset` discharges the named [TZ24]
hypothesis `TZPrimeSupply 4 4 7` from the seven explicit primes `257,…,317 ≡ 1 (mod 4)` in the
window `[256,512]` (which dwarf the bad-prime budget `12·½ = 6 < 7`); feeding that through the
conditional headline `KKH26PolyFieldCeiling.kkh26_mcaDeltaStar_le_of_TZ` yields:

> **`kkh26_mcaDeltaStar_le_concrete`** — an actual prime `p ∈ [256,512]`, `p ≡ 1 (mod 4)`, a smooth
> domain `⟨g⟩ ⊆ F_p^×` of order `4`, and `mcaDeltaStar(evalCode g 4 0, ε*) ≤ 1 − 2/2² = 1/2` for
> every `ε* < 4/p`.

This certifies the entire chain — supply → good-prime collision-avoidance → [KKH26] Lemma 1
separation → witness spread → δ* ceiling — is non-vacuous and correctly wired (not merely
conditionally stated).  The code is degree-0 (the largest `μ` for which the bad-prime budget stays
listable with `decide`-checkable primes); the value is the full-machine instantiation, not the
code.  Axiom-clean.  Issue #334 (B3).
-/

open Finset
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.KKH26

/-- **A fully concrete, machine-checked [KKH26] δ\* ceiling at polynomial field size.**

Wiring the explicit-prime supply `TZPrimeSupply 4 4 7` (the window `[4⁴, 2·4⁴] = [256, 512]`
contains the seven primes `257, 269, 277, 281, 293, 313, 317 ≡ 1 (mod 4)`, dwarfing the bad-prime
budget `|collisionPairs 2 2|·log 16 / log(4⁴) = 12·½ = 6 < 7`) through the conditional headline
`kkh26_mcaDeltaStar_le_of_TZ`, we obtain — with **no analytic number theory** — an actual prime
`p ∈ [256, 512]`, `p ≡ 1 (mod 4)`, a smooth domain `⟨g⟩ ⊆ F_p^×` of order `4`, and the δ\* ceiling

  `mcaDeltaStar(evalCode g 4 0, ε*) ≤ 1 − 2/2² = 1/2`   for every `ε* < 4/p`.

This is the entire B3 machine — [TZ24] supply → good-prime avoidance of every collision resultant →
[KKH26] Lemma 1 separation → witness spread → δ\* ceiling — exercised end-to-end on an explicit
code, certifying it is non-vacuous and correctly wired, not merely conditionally stated. -/
theorem kkh26_mcaDeltaStar_le_concrete :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 4] ∧
      ((4 : ℕ) : ℝ) ^ ((4 : ℕ) : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((4 : ℕ) : ℝ) ^ ((4 : ℕ) : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 4 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 4 ((2 - 2) * 1)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  -- the explicit-prime supply
  have tzS : TZPrimeSupply 4 ((4 : ℕ) : ℝ) 7 := by
    refine tzPrimeSupply_of_subset (S := {257, 269, 277, 281, 293, 313, 317})
      (fun p hp => ?_) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by norm_num, by decide, by rw [Real.rpow_natCast]; norm_num,
        by rw [Real.rpow_natCast]; norm_num⟩
  -- feed it through the conditional headline
  refine kkh26_mcaDeltaStar_le_of_TZ tzS (μ := 2) (m := 1) (r := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [Real.rpow_natCast]; norm_num) (by rw [Real.rpow_natCast]; norm_num) ?_
  -- the bad-prime budget: 12 · log 16 / log(4⁴) = 6 < 7
  have hlog2 : Real.log 2 ≠ 0 := by
    simpa using Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  rw [hc, Real.rpow_natCast]
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num; rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have h256 : Real.log (((4 : ℕ) : ℝ) ^ (4 : ℕ)) = 8 * Real.log 2 := by
    rw [show ((4 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← pow_mul, Real.log_pow]
    push_cast; ring
  rw [h16, h256, mul_div_mul_right _ _ hlog2]
  norm_num

end ArkLib.ProximityGap.KKH26

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete
