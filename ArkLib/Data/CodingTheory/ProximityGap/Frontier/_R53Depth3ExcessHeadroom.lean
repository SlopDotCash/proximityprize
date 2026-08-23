/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R50Depth3WraparoundVanishing

/-!
# LANE B2 (#466 round 53): THE HEADROOM REDUCTION — the depth-3 rung needs only a BOUNDED
  wraparound excess, not exact vanishing

Round 50 named the depth-3 atom as exact equality `addEnergy3 G = 15n³−45n²+40n`
(`Depth3WraparoundVanishing`).  Round 52 refuted that as a UNIVERSAL statement: sparse bad
primes carry a genuine nonzero char-`p` wraparound excess (measured up to `β ≈ 6.3` at
`n = 32`).  But the same probe showed the excess is only `O(n²)` — at every bad prime,
`E₃/(15n³) ∈ [2.06, 2.10]/2.5`, i.e. the excess never came close to breaking the Wick bound.

This brick explains WHY, and turns the numerical finding into a typed reduction.

**The headroom.**  The characteristic-zero closed form is `15n³ − 45n² + 40n` — that is the
Wick value `15n³` MINUS a positive `Θ(n²)` term.  So there is a built-in slack of `≈ 45n²`
below the exact Wick bound.  The finite-field energy is `charZero + excess`; as long as the
char-`p` excess stays within that `45n²` headroom, the EXACT Wick bound `GaussianEnergyBound G 3`
still holds — no exact vanishing required.

**What this buys.**  The r = 3 rung's open input is downgraded from the (false) exact-vanishing
atom to the strictly weaker, probe-consistent:

  **`Depth3ExcessBounded G E`** : `addEnergy3 G ≤ (15n³ − 45n² + 40n) + E`,

and the reduction `gaussianEnergyBound_three_of_excess_headroom`: if `E ≤ 45n² − 40n` and
`1 ≤ n`, then `GaussianEnergyBound G 3` (exact Wick).  The concrete corollary
`gaussianEnergyBound_three_of_quadraticExcess` instantiates `E = C·n²` with the r52-measured
regime `C ≤ 44`, `n ≥ 40` — the r52 data has `C ≈ 4`, an order of magnitude inside the gate.

The open content is now: *the char-`p` depth-3 wraparound excess of `μ_n` is `≤ 45n² − 40n`* —
a one-sided `O(n²)` bound, not an exact cyclotomic identity.  Same wall class as before, but a
much smaller and more plausible target.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 53, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.Frontier.R50Depth3WraparoundVanishing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The refined depth-3 atom (round 53).**  The finite-field depth-3 additive energy is at
most the characteristic-zero closed form plus a nonnegative excess `E`.  This is the
one-sided upper-bound weakening of the round-50 exact-equality `Depth3WraparoundVanishing`;
round-52 numerics put `E = O(n²)`. -/
def Depth3ExcessBounded (G : Finset F) (E : ℝ) : Prop :=
  (addEnergy3 G : ℝ)
    ≤ (15 * (G.card : ℝ) ^ 3 - 45 * (G.card : ℝ) ^ 2 + 40 * (G.card : ℝ)) + E

/-- **THE HEADROOM REDUCTION (round-53 main theorem).**  If the char-`p` depth-3 excess `E`
fits within the char-0 headroom `45n² − 40n`, then the EXACT Wick energy bound
`GaussianEnergyBound G 3` holds — no exact wraparound-vanishing needed. -/
theorem gaussianEnergyBound_three_of_excess_headroom {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {E : ℝ} (hexc : Depth3ExcessBounded G E)
    (hhead : E ≤ 45 * (G.card : ℝ) ^ 2 - 40 * (G.card : ℝ)) :
    GaussianEnergyBound G 3 := by
  unfold GaussianEnergyBound
  have hbridge : (rEnergy G 3 : ℝ) = (addEnergy3 G : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (rEnergy_three_eq_addEnergy3 hψ G)
  have hdf : (Nat.doubleFactorial (2 * 3 - 1) : ℝ) = 15 := by
    norm_num [Nat.doubleFactorial]
  rw [hbridge, hdf]
  -- addEnergy3 ≤ (15n³ − 45n² + 40n) + E ≤ (15n³ − 45n² + 40n) + (45n² − 40n) = 15n³
  calc (addEnergy3 G : ℝ)
      ≤ (15 * (G.card : ℝ) ^ 3 - 45 * (G.card : ℝ) ^ 2 + 40 * (G.card : ℝ)) + E := hexc
    _ ≤ (15 * (G.card : ℝ) ^ 3 - 45 * (G.card : ℝ) ^ 2 + 40 * (G.card : ℝ))
          + (45 * (G.card : ℝ) ^ 2 - 40 * (G.card : ℝ)) := by linarith
    _ = 15 * (G.card : ℝ) ^ 3 := by ring

/-- The `45n² − 40n` headroom absorbs any quadratic excess `C·n²` with `C ≤ 44`, once
`n ≥ 40`.  (Both slack conditions are enormous relative to the r52-measured `C ≈ 4`.) -/
theorem quadraticExcess_within_headroom (G : Finset F) {C : ℝ}
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ)) :
    C * (G.card : ℝ) ^ 2 ≤ 45 * (G.card : ℝ) ^ 2 - 40 * (G.card : ℝ) := by
  -- 45n² − 40n − Cn² = (45−C)n² − 40n ≥ n² − 40n = n(n − 40) ≥ 0
  have hn0 : (0:ℝ) ≤ (G.card : ℝ) := le_trans (by norm_num) hn
  nlinarith [hn, hn0, hC, sq_nonneg ((G.card : ℝ))]

/-- **Concrete corollary from the r52 regime.**  If the depth-3 excess is quadratic with
constant `C ≤ 44` (r52 measured `C ≈ 4`) and `n ≥ 40`, the exact Wick energy bound holds. -/
theorem gaussianEnergyBound_three_of_quadraticExcess {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {C : ℝ}
    (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ)) :
    GaussianEnergyBound G 3 :=
  gaussianEnergyBound_three_of_excess_headroom hψ G hexc
    (quadraticExcess_within_headroom G hC hn)

/-- **Sixth-moment form.**  Under the same headroom hypothesis, the sixth Gauss-sum moment
obeys the clean Wick estimate `∑_b ‖η_b‖⁶ ≤ 15·q·|G|³`. -/
theorem sixthMoment_le_of_excess_headroom {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {E : ℝ} (hexc : Depth3ExcessBounded G E)
    (hhead : E ≤ 45 * (G.card : ℝ) ^ 2 - 40 * (G.card : ℝ)) :
    ∑ b : F, ‖eta ψ G b‖ ^ 6 ≤ (Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3) := by
  have hE : (addEnergy3 G : ℝ) ≤ 15 * (G.card : ℝ) ^ 3 := by
    calc (addEnergy3 G : ℝ)
        ≤ (15 * (G.card : ℝ) ^ 3 - 45 * (G.card : ℝ) ^ 2 + 40 * (G.card : ℝ)) + E := hexc
      _ ≤ (15 * (G.card : ℝ) ^ 3 - 45 * (G.card : ℝ) ^ 2 + 40 * (G.card : ℝ))
            + (45 * (G.card : ℝ) ^ 2 - 40 * (G.card : ℝ)) := by linarith
      _ = 15 * (G.card : ℝ) ^ 3 := by ring
  rw [subgroup_gaussSum_sixthMoment hψ G]
  exact mul_le_mul_of_nonneg_left hE (by exact_mod_cast Nat.zero_le (Fintype.card F))

/-- **The exact-vanishing atom is a special case.**  Round-50 `Depth3WraparoundVanishing` with
the char-0 closed form is `Depth3ExcessBounded G 0` — the reduction here strictly generalizes
the round-50 bridge (headroom `45n² − 40n ≥ 0`). -/
theorem depth3ExcessBounded_zero_of_closedForm (G : Finset F)
    (hvan : (addEnergy3 G : ℝ)
        = 15 * (G.card : ℝ) ^ 3 - 45 * (G.card : ℝ) ^ 2 + 40 * (G.card : ℝ)) :
    Depth3ExcessBounded G 0 := by
  unfold Depth3ExcessBounded
  rw [hvan]; linarith

end ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom.gaussianEnergyBound_three_of_excess_headroom
#print axioms
  ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom.quadraticExcess_within_headroom
#print axioms
  ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom.gaussianEnergyBound_three_of_quadraticExcess
#print axioms
  ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom.sixthMoment_le_of_excess_headroom
