/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKLaterTransitionDefectLedgers

/-!
# Dominant-pair split socket for the two late Newton transitions

For the subset Newton recursion, let `E_jk` denote the centered covariance of the physical
histograms

`U_j(y) = sum_(x in G) a_(r+1-j)(y-j*x)`.

The signed Newton energy is the sum of `(-1)^(j+k) E_jk`.  Exact finite-cell reconnaissance
shows that its leading two-colour part

`L = E_11 + E_22 - 2 E_12`

is the nonzero-frequency energy of `eta_b * e_r(b) - eta_(2b) * e_(r-1)(b)`, while the remainder
`R` contains every matrix cell touching a colour `j >= 3`.  The physical identities should give

`36 * Delta_6 = L_5 + R_5`,
`49 * Delta_7 = L_6 + R_6`.

This file deliberately does **not** assert those arithmetic estimates.  It proves only the exact
abstract scalar consumer suggested by that split.  At `5 -> 6`, allocate the unscaled distributed
cap `10.5` to `L_5` and the robust overhead `0.021` to `R_5`; the numerators add as
`10500 + 21 = 10521`.  At `6 -> 7`, the corresponding allocation is `12.5 + 0.025`, with
`12500 + 25 = 12525`.  These are exactly the existing robust distributed ledgers, not new slack.

All quantities here are integers, so a future weighted-collision theorem can feed the socket
without rational denominator management.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.BGKLateNewtonDominantPairSocket

open BGKLaterTransitionDefectLedgers

/-- The intended two-colour Newton energy `E_11 + E_22 - 2 E_12`.  No sign assumption is needed
by the scalar consumer. -/
def dominantPairEnergy (E11 E22 E12 : Int) : Int := E11 + E22 - 2 * E12

/-- Abstract exact split of the `5 -> 6` signed Newton energy. -/
def FifthNewtonSplit (D : Nat -> Int) (leading tail : Int) : Prop :=
  36 * D 6 = leading + tail

/-- Allocate the unscaled half-unit cap `10.5` to the dominant pair at `5 -> 6`. -/
def FifthDominantPairBudget (D : Nat -> Int) (leading : Int) : Prop :=
  (1000 : Int) * productionN * leading <=
    10500 * (productionN - 5 : Int) ^ 2 * D 5

/-- Allocate only the robust overhead `0.021` to the remaining Newton terms at `5 -> 6`. -/
def FifthTailBudget (D : Nat -> Int) (tail : Int) : Prop :=
  (1000 : Int) * productionN * tail <=
    21 * (productionN - 5 : Int) ^ 2 * D 5

/-- The exact split budgets add to the existing numerator `10521`. -/
theorem robust_halfUnit_five_of_dominantPair_and_tail
    (D : Nat -> Int) (leading tail : Int)
    (hsplit : FifthNewtonSplit D leading tail)
    (hleading : FifthDominantPairBudget D leading)
    (htail : FifthTailBudget D tail) :
    RationalTransitionAt productionN 5 (21 * 501) 1000 D := by
  rw [robust_halfUnit_five_iff]
  simp only [FifthNewtonSplit] at hsplit
  simp only [FifthDominantPairBudget] at hleading
  simp only [FifthTailBudget] at htail
  calc
    (1000 : Int) * productionN * 36 * D 6 =
        1000 * productionN * (36 * D 6) := by ring
    _ = 1000 * productionN * (leading + tail) := by rw [hsplit]
    _ = 1000 * productionN * leading + 1000 * productionN * tail := by ring
    _ <= 10500 * (productionN - 5 : Int) ^ 2 * D 5 +
        21 * (productionN - 5 : Int) ^ 2 * D 5 := add_le_add hleading htail
    _ = 10521 * (productionN - 5 : Int) ^ 2 * D 5 := by ring

/-- Abstract exact split of the `6 -> 7` signed Newton energy. -/
def SixthNewtonSplit (D : Nat -> Int) (leading tail : Int) : Prop :=
  49 * D 7 = leading + tail

/-- Allocate the unscaled half-unit cap `12.5` to the dominant pair at `6 -> 7`. -/
def SixthDominantPairBudget (D : Nat -> Int) (leading : Int) : Prop :=
  (1000 : Int) * productionN * leading <=
    12500 * (productionN - 6 : Int) ^ 2 * D 6

/-- Allocate only the robust overhead `0.025` to the remaining Newton terms at `6 -> 7`. -/
def SixthTailBudget (D : Nat -> Int) (tail : Int) : Prop :=
  (1000 : Int) * productionN * tail <=
    25 * (productionN - 6 : Int) ^ 2 * D 6

/-- The exact split budgets add to the existing numerator `12525`. -/
theorem robust_halfUnit_six_of_dominantPair_and_tail
    (D : Nat -> Int) (leading tail : Int)
    (hsplit : SixthNewtonSplit D leading tail)
    (hleading : SixthDominantPairBudget D leading)
    (htail : SixthTailBudget D tail) :
    RationalTransitionAt productionN 6 (25 * 501) 1000 D := by
  rw [robust_halfUnit_six_iff]
  simp only [SixthNewtonSplit] at hsplit
  simp only [SixthDominantPairBudget] at hleading
  simp only [SixthTailBudget] at htail
  calc
    (1000 : Int) * productionN * 49 * D 7 =
        1000 * productionN * (49 * D 7) := by ring
    _ = 1000 * productionN * (leading + tail) := by rw [hsplit]
    _ = 1000 * productionN * leading + 1000 * productionN * tail := by ring
    _ <= 12500 * (productionN - 6 : Int) ^ 2 * D 6 +
        25 * (productionN - 6 : Int) ^ 2 * D 6 := add_le_add hleading htail
    _ = 12525 * (productionN - 6 : Int) ^ 2 * D 6 := by ring

/-- Consolidated two-late-transition consumer.  The four budget hypotheses are precisely the
new arithmetic sockets; all remaining work is deterministic ledger addition. -/
theorem robust_distributedLate_of_dominantPair_and_tail
    (D : Nat -> Int) (leadingFive tailFive leadingSix tailSix : Int)
    (hsplitFive : FifthNewtonSplit D leadingFive tailFive)
    (hleadingFive : FifthDominantPairBudget D leadingFive)
    (htailFive : FifthTailBudget D tailFive)
    (hsplitSix : SixthNewtonSplit D leadingSix tailSix)
    (hleadingSix : SixthDominantPairBudget D leadingSix)
    (htailSix : SixthTailBudget D tailSix) :
    RationalTransitionAt productionN 5 (21 * 501) 1000 D /\
      RationalTransitionAt productionN 6 (25 * 501) 1000 D := by
  exact ⟨
    robust_halfUnit_five_of_dominantPair_and_tail
      D leadingFive tailFive hsplitFive hleadingFive htailFive,
    robust_halfUnit_six_of_dominantPair_and_tail
      D leadingSix tailSix hsplitSix hleadingSix htailSix⟩

/-! ## Axiom audit -/

#print axioms robust_halfUnit_five_of_dominantPair_and_tail
#print axioms robust_halfUnit_six_of_dominantPair_and_tail
#print axioms robust_distributedLate_of_dominantPair_and_tail

end ArkLib.ProximityGap.Frontier.BGKLateNewtonDominantPairSocket
