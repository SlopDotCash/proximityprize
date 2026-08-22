/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R240GeneralRFoldVariance

/-!
# G81 (#466): unconditional deep-rung DC recovery

The DC-subtracted prize hypothesis `DCEnergyBound G r`
(`q·E_r(G) − |G|^{2r} ≤ q·(2r−1)‼·|G|^r`) holds **outright** — no character-sum
input, no BGK, no Weil — as soon as the Wick factor dominates the raw
representation mass: `(2r−1)‼ ≥ |G|^r`.

The mechanism is the crude energy ceiling

```text
E_r(G) = Σ_c repR(c)² ≤ (Σ_c repR(c))² = |G|^{2r},
```

which sits inside the Wick budget once `(2r−1)‼ ≥ |G|^r`, because then
`q·E_r − |G|^{2r} ≤ q·|G|^{2r} = q·|G|^r·|G|^r ≤ q·(2r−1)‼·|G|^r`.

**Consequence.** The open rung window of the CORE wall is bounded ABOVE
unconditionally: only depths `r` with `(2r−1)‼ < n^r` (roughly `r ≲ e·n/2`,
where `n = |G|`) can fail. This matches the observed probe recovery (G75
entry: structured cells return under budget near `r ≈ n/2`).

**Honest scope — no prize contact.** The prize depth is `r ≈ log p ≪ n`,
which sits far inside the window where `(2r−1)‼ < n^r`; there the crude
ceiling `E_r ≤ n^{2r}` is far above Wick and this file says nothing. This is
a ceiling pin on the deep end of the rung ladder, NOT a prize rung. CORE
remains OPEN.

Issue #466 G81.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.G81DeepRungDCRecovery

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Crude energy ceiling.** `E_r(G) ≤ |G|^{2r}`: the `L²` mass of the
`r`-fold representation function is at most the square of its total mass. -/
theorem rEnergy_le_card_pow (G : Finset F) (r : ℕ) :
    rEnergy G r ≤ G.card ^ (2 * r) := by
  rw [rEnergy_eq_sum_repR_sq G r]
  calc ∑ c : F, (repR G r c) ^ 2
      ≤ ∑ c : F, repR G r c * G.card ^ r := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [sq]
        refine Nat.mul_le_mul_left _ ?_
        calc repR G r c ≤ ∑ c' : F, repR G r c' :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
          _ = G.card ^ r := sum_repR G r
    _ = (∑ c : F, repR G r c) * G.card ^ r := (Finset.sum_mul _ _ _).symm
    _ = G.card ^ r * G.card ^ r := by rw [sum_repR]
    _ = G.card ^ (2 * r) := by rw [two_mul, pow_add]

/-- **Unconditional deep-rung recovery.** Once the Wick factor dominates the
raw mass — `(2r−1)‼ ≥ |G|^r` — the DC-subtracted prize hypothesis
`DCEnergyBound G r` holds outright, via the crude ceiling
`E_r ≤ |G|^{2r} = |G|^r·|G|^r ≤ (2r−1)‼·|G|^r`. -/
theorem dcEnergyBound_of_doubleFactorial_ge (G : Finset F) (r : ℕ)
    (h : G.card ^ r ≤ Nat.doubleFactorial (2 * r - 1)) :
    DCEnergyBound G r := by
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  have hE : (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by
    exact_mod_cast rEnergy_le_card_pow G r
  have hcast : (G.card : ℝ) ^ r ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) := by
    exact_mod_cast h
  have hpow : (G.card : ℝ) ^ (2 * r)
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
    have hsplit : (G.card : ℝ) ^ (2 * r) = (G.card : ℝ) ^ r * (G.card : ℝ) ^ r := by
      rw [← pow_add, two_mul]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hcast (by positivity)
  have hmain : (Fintype.card F : ℝ) * (rEnergy G r : ℝ)
      ≤ (Fintype.card F : ℝ)
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
    mul_le_mul_of_nonneg_left (hE.trans hpow) hq
  have hnn : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by positivity
  unfold DCEnergyBound
  linarith

/-- Sanity anchor for the arithmetic criterion: `5‼ = 15`. -/
theorem doubleFactorial_five : Nat.doubleFactorial 5 = 15 := by decide

/-- **Concrete instance.** At depth `r = 3`, any `G` with `|G| = 2` satisfies
the DC target unconditionally: `2³ = 8 ≤ 15 = 5‼ = (2·3−1)‼`. -/
theorem dcEnergyBound_card_two_depth_three (G : Finset F) (h2 : G.card = 2) :
    DCEnergyBound G 3 :=
  dcEnergyBound_of_doubleFactorial_ge G 3 (by rw [h2]; decide)

end ArkLib.ProximityGap.Frontier.G81DeepRungDCRecovery

#print axioms ArkLib.ProximityGap.Frontier.G81DeepRungDCRecovery.rEnergy_le_card_pow
#print axioms ArkLib.ProximityGap.Frontier.G81DeepRungDCRecovery.dcEnergyBound_of_doubleFactorial_ge
#print axioms ArkLib.ProximityGap.Frontier.G81DeepRungDCRecovery.doubleFactorial_five
#print axioms ArkLib.ProximityGap.Frontier.G81DeepRungDCRecovery.dcEnergyBound_card_two_depth_three
