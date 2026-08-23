/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Data.CodingTheory.ProximityGap.MCAUpToCapacityFalse

/-!
# A one-sided resolution witness for the Grand MCA Challenge (#232)

`GrandChallenges.MCAUpperWitness C ε*` is the issue's data structure for *upper one-sided
progress*: a radius `δ` with `ε_mca(C, δ) > ε*`, which forces any resolution's threshold to satisfy
`δ* ≤ δ`. This file constructs such a witness for Reed–Solomon from the admit-free MCA refutation
`ProximityGap.MCANearCapacityGK.rs_mca_uptoCapacity_false_of_smallField`.

> **`rs_mcaUpperWitness`**: for an RS code with `1 ≤ k ≤ n` over a field with `|F| < (n−k)·2^128`,
> the radius `δ = 1 − (k+1)/n` is a certified `MCAUpperWitness` at the prize threshold `ε* = 2^{-128}`.

So the prize threshold `δ*` for these codes provably satisfies `δ* ≤ 1 − (k+1)/n` (strictly below
capacity). This pins the *upper* end of the `δ*` search interval, machine-checked and axiom-clean —
genuine, if partial, progress on the positive Grand MCA Challenge's resolution data.

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap.GrandChallenges

open scoped NNReal ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

/-- **An `MCAUpperWitness` for Reed–Solomon from the sunflower MCA refutation.** For `1 ≤ k ≤ n`
and a field with `|F| < (n−k)·2^128`, the near-capacity radius `δ = 1 − (k+1)/n` certifies
`ε_mca(RS, δ) > ε*`, so the MCA threshold satisfies `δ* ≤ δ`. -/
noncomputable def rs_mcaUpperWitness [NeZero n] (domain : Fin n ↪ F) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ n) (hsmall : (Fintype.card F : ℝ) < ((n - k : ℕ) : ℝ) * 2 ^ 128) :
    MCAUpperWitness (ReedSolomon.code (domain := domain) k : Set (Fin n → F)) epsStar where
  δ := 1 - ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0)
  exceeds := by
    have h := MCANearCapacityGK.rs_mca_uptoCapacity_false_of_smallField domain k hk hkn hsmall
    have hcoe : (epsStar : ENNReal) = ENNReal.ofReal (1 / 2 ^ 128) := by
      have he : (epsStar : ℝ) = 1 / 2 ^ 128 := by simp [epsStar]
      rw [← he, ENNReal.ofReal_coe_nnreal]
    rw [gt_iff_lt, hcoe]
    exact h

#print axioms rs_mcaUpperWitness

end ProximityGap.GrandChallenges
