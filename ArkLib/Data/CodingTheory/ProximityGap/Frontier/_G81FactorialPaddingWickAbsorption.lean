/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G79SPrimitivePaddingSaddleLocalization

/-!
# G81: the missing padding factorial can be paid by the unused Wick head

G80R refuted the raw R369 padding envelope: independently ordering the common padding multiset
costs up to `(r-s)!`.  This file proves that this correction does not automatically kill the
saddle strategy.  The odd Wick factorial splits into its top `s` factors and its lower `r-s`
factors, and the latter dominate `(r-s)!`.

Consequently the factorial-corrected sector envelope is still absorbed by the *full* Wick budget
under the same normalized primitive-sector condition `J*r^s <= n^s`.  This is an arithmetic
consumer only: proving a corrected combinatorial envelope for the actual collision sector remains
open. Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G81FactorialPaddingWickAbsorption

open ArkLib.ProximityGap.Frontier.G79PrimitivePaddingSaddleLocalization

/-- The lower Wick head dominates the factorial of the same depth. -/
theorem factorial_le_oddDoubleFactorial : ∀ t : ℕ,
    t.factorial ≤ Nat.doubleFactorial (2 * t - 1)
  | 0 => by simp
  | t + 1 => by
      have ih := factorial_le_oddDoubleFactorial t
      by_cases ht : t = 0
      · subst ht
        simp
      · have harg : 2 * (t + 1) - 1 = (2 * t - 1) + 2 := by omega
        rw [Nat.factorial, harg, Nat.doubleFactorial_add_two]
        exact Nat.mul_le_mul (by omega) ih

/-- Splitting the odd Wick double factorial after its top `s` factors. -/
theorem oddDoubleFactorial_split {r s : ℕ} (hsr : s ≤ r) :
    Nat.doubleFactorial (2 * r - 1) =
      oddWickTail r s * Nat.doubleFactorial (2 * (r - s) - 1) := by
  induction s with
  | zero => simp [oddWickTail]
  | succ s ih =>
      have hsr' : s ≤ r := Nat.le_trans (Nat.le_succ s) hsr
      have hrs : s < r := Nat.lt_of_succ_le hsr
      have hsub : r - s = (r - (s + 1)) + 1 := by omega
      have htail : oddWickTail r (s + 1) =
          oddWickTail r s * (2 * (r - s) - 1) := by
        simp [oddWickTail, Finset.prod_range_succ]
      have hdf : Nat.doubleFactorial (2 * (r - s) - 1) =
          (2 * (r - s) - 1) *
            Nat.doubleFactorial (2 * (r - (s + 1)) - 1) := by
        by_cases hu : r - (s + 1) = 0
        · have : r = s + 1 := by omega
          subst r
          simp
        · have harg : 2 * (r - s) - 1 =
              (2 * (r - (s + 1)) - 1) + 2 := by omega
          rw [harg, Nat.doubleFactorial_add_two]
      calc
        Nat.doubleFactorial (2 * r - 1) =
            oddWickTail r s * Nat.doubleFactorial (2 * (r - s) - 1) := ih hsr'
        _ = oddWickTail r s * (2 * (r - s) - 1) *
            Nat.doubleFactorial (2 * (r - (s + 1)) - 1) := by rw [hdf]; ring
        _ = oddWickTail r (s + 1) *
            Nat.doubleFactorial (2 * (r - (s + 1)) - 1) := by rw [htail]

/-- The factorial-corrected padding envelope exposed by G80R. -/
def correctedPadEnvelope (n r J s : ℕ) : ℕ :=
  J * (r.descFactorial s) ^ 2 * (r - s).factorial * n ^ (r - s)

/-- **Corrected saddle absorption.** Even after paying the missing `(r-s)!` padding-order
multiplicity, a sector satisfying `J*r^s <= n^s` fits in the full Wick budget. -/
theorem correctedPaddedSector_le_fullWick
    {n r J s W : ℕ}
    (hrs : 2 * s ≤ r + 1)
    (hsr : s ≤ r)
    (hW : W ≤ correctedPadEnvelope n r J s)
    (hJ : J * r ^ s ≤ n ^ s) :
    W ≤ Nat.doubleFactorial (2 * r - 1) * n ^ r := by
  have hfall : r.descFactorial s ≤ r ^ s := Nat.descFactorial_le_pow r s
  have htail := pow_le_oddWickTail hrs
  have hfac := factorial_le_oddDoubleFactorial (r - s)
  calc
    W ≤ correctedPadEnvelope n r J s := hW
    _ ≤ J * r ^ (2 * s) * (r - s).factorial * n ^ (r - s) := by
      unfold correctedPadEnvelope
      have hsq : (r.descFactorial s) ^ 2 ≤ r ^ (2 * s) := by
        calc
          (r.descFactorial s) ^ 2 ≤ (r ^ s) ^ 2 := Nat.pow_le_pow_left hfall 2
          _ = r ^ (2 * s) := by ring
      exact Nat.mul_le_mul_right (n ^ (r - s))
        (Nat.mul_le_mul_right (r - s).factorial (Nat.mul_le_mul_left J hsq))
    _ = (J * r ^ s) * r ^ s * (r - s).factorial * n ^ (r - s) := by ring
    _ ≤ n ^ s * oddWickTail r s *
        Nat.doubleFactorial (2 * (r - s) - 1) * n ^ (r - s) := by gcongr
    _ = (oddWickTail r s * Nat.doubleFactorial (2 * (r - s) - 1)) *
        (n ^ s * n ^ (r - s)) := by ring
    _ = Nat.doubleFactorial (2 * r - 1) * n ^ r := by
      rw [← oddDoubleFactorial_split hsr, ← pow_add, Nat.add_sub_of_le hsr]

end ArkLib.ProximityGap.Frontier.G81FactorialPaddingWickAbsorption

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G81FactorialPaddingWickAbsorption.factorial_le_oddDoubleFactorial
#print axioms
  ArkLib.ProximityGap.Frontier.G81FactorialPaddingWickAbsorption.oddDoubleFactorial_split
#print axioms
  ArkLib.ProximityGap.Frontier.G81FactorialPaddingWickAbsorption.correctedPaddedSector_le_fullWick
