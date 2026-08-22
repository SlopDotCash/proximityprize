/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G253AntisortedSignReversal

/-!
# G254: conjugate-row symmetry does not repair the global phase-discrepancy route (#466)

G252/G253 show that a phase-histogram constraint cannot lower-bound the fixed-row weighted
covariance: a balanced phase reassignment can annihilate, then reverse, the signal.  The actual
quotient-character family has one additional mandatory invariant not represented in G253.  Since
the physical profiles are real, rows `χ` and `χ⁻¹` occur as conjugate pairs.  Any honest phase
reassignment must preserve those pairs.

This file audits that possible repair.  Index the nonprincipal rows by `2*k` inverse-character
pairs, each with two conjugate members.  Give both members of a pair the same real rank weight and
the same sign.  The sign assignment is therefore conjugation-preserving.  Assign `+1` to the `k`
low-weight pairs and `-1` to the `k` high-weight pairs.  It is still exactly histogram-balanced on
the full `4*k` rows, and its covariance is

```text
pairedSplitCov a k = -2*k^2.
```

Thus mandatory conjugation symmetry only doubles G253's reversal; it does not obstruct it.
The exact companion probe computes the real `W_G,R_5,R_6` quotient profiles, verifies
`hat f(χ⁻¹)=conj(hat f(χ))`, restricts signs to inverse-character pairs, and obtains strict reversal
in all six proper-subgroup cells (`pairedFrac` from `-0.84` to `-0.96`).

This closes only the conjugate-symmetry repair of the Cartesian/global-discrepancy route.  It is not
a Jacobi estimate and not a prize closure.  A surviving certificate must control actual joint
phase-row placement directly, beyond both the global histogram and its conjugation symmetry.
CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G254ConjugatePairedPhaseFreedom

open Finset
open ArkLib.ProximityGap.Frontier.G253AntisortedSignReversal

/-- A quotient row together with its conjugate mate.  The first coordinate indexes the inverse-
character pair; the second chooses one of its two members. -/
abbrev PairedRow (k : ℕ) := Fin (2 * k) × Fin 2

/-- Conjugate mates carry the same real fixed-row weight. -/
def pairedWeight (a k : ℕ) : PairedRow k → ℤ :=
  fun x => rankWeight a k x.1

/-- A conjugation-preserving balanced sign: both members of a low pair get `+1`, both members of a
high pair get `-1`. -/
def pairedSign (k : ℕ) : PairedRow k → ℤ :=
  fun x => antiSign k x.1

/-- Aligned covariance on all members of the conjugate pairs. -/
def pairedAlignedCov (a k : ℕ) : ℤ := ∑ x : PairedRow k, pairedWeight a k x

/-- Covariance after the conjugation-preserving balanced move. -/
def pairedSplitCov (a k : ℕ) : ℤ :=
  ∑ x : PairedRow k, pairedSign k x * pairedWeight a k x

/-- Pair duplication doubles the aligned covariance. -/
theorem pairedAlignedCov_eq (a k : ℕ) : pairedAlignedCov a k = 2 * alignedCov a k := by
  unfold pairedAlignedCov pairedWeight alignedCov
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  calc
    ∑ x, (rankWeight a k x + rankWeight a k x) =
        ∑ x, 2 * rankWeight a k x := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 2 * ∑ x, rankWeight a k x := by rw [Finset.mul_sum]

/-- Pair duplication preserves exact histogram balance: the full `4k`-row sign sum is zero. -/
theorem pairedSign_histogram (k : ℕ) : ∑ x : PairedRow k, pairedSign k x = 0 := by
  unfold pairedSign
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  calc
    ∑ x, (antiSign k x + antiSign k x) = ∑ x, 2 * antiSign k x := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 2 * ∑ x, antiSign k x := by rw [Finset.mul_sum]
    _ = 0 := by rw [antiSign_histogram]; ring

/-- Pair duplication doubles G253's split covariance. -/
theorem pairedSplitCov_eq_two_mul (a k : ℕ) :
    pairedSplitCov a k = 2 * splitCov a k := by
  unfold pairedSplitCov pairedSign pairedWeight splitCov
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  calc
    ∑ x, (antiSign k x * rankWeight a k x + antiSign k x * rankWeight a k x) =
        ∑ x, 2 * (antiSign k x * rankWeight a k x) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 2 * ∑ x, antiSign k x * rankWeight a k x := by rw [Finset.mul_sum]

/-- **Conjugate-paired reversal, closed form.**  The honest paired move has covariance `-2k²`. -/
theorem pairedSplitCov_eq_neg_two_sq (a k : ℕ) :
    pairedSplitCov a k = -2 * (k : ℤ) ^ 2 := by
  rw [pairedSplitCov_eq_two_mul, splitCov_eq_neg_sq]
  ring

/-- The paired move strictly reverses the covariance for every nonempty family. -/
theorem pairedSplitCov_neg (a k : ℕ) (hk : 0 < k) : pairedSplitCov a k < 0 := by
  rw [pairedSplitCov_eq_neg_two_sq]
  have : (0 : ℤ) < (k : ℤ) ^ 2 := by positivity
  nlinarith

/-- The aligned paired covariance is positive for every nonempty family. -/
theorem pairedAlignedCov_pos (a k : ℕ) (hk : 0 < k) : 0 < pairedAlignedCov a k := by
  rw [pairedAlignedCov_eq]
  have := alignedCov_pos a k hk
  positivity

/-- **Headline no-go.**  Even after enforcing inverse-character pairing, an exactly balanced,
conjugation-preserving phase move reverses a positive fixed-row covariance. -/
theorem conjugation_symmetry_does_not_pin_covariance (a k : ℕ) (hk : 0 < k) :
    0 < pairedAlignedCov a k ∧ pairedSplitCov a k < 0 ∧
      ∑ x : PairedRow k, pairedSign k x = 0 :=
  ⟨pairedAlignedCov_pos a k hk, pairedSplitCov_neg a k hk, pairedSign_histogram k⟩

/-- Honest scope marker. -/
def isPrizeClosure : Bool := false

theorem not_prizeClosure : isPrizeClosure = false := rfl

#print axioms pairedAlignedCov_eq
#print axioms pairedSign_histogram
#print axioms pairedSplitCov_eq_two_mul
#print axioms pairedSplitCov_eq_neg_two_sq
#print axioms pairedSplitCov_neg
#print axioms pairedAlignedCov_pos
#print axioms conjugation_symmetry_does_not_pin_covariance
#print axioms not_prizeClosure

end ArkLib.ProximityGap.Frontier.G254ConjugatePairedPhaseFreedom
