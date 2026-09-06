/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sol
-/
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyEssential

/-!
# The thesis-capstone good-prime premises force the RAW energy bound — vacuous at prize
(#444 / #407)

The adversarial audit (`DISPROOF_LOG.md`, 2026-06-19) confirmed
`_ThesisCapstone.subPoisson_variance_
implies_prizeFloor` is vacuous-at-prize: its STEP-2 energy bridge derives
`hEbound : E_r ≤ (2r·|G|)^r` (the **raw, DC-included** energy bound = `GaussPeriodMomentBound.
GaussianEnergyBound`) from `hwrap` (`E_r = E0 + W`), `hanchor` (`E0 + slack ≤ Wick`), and
the good-prime
selection (`W ≤ slack`), then feeds the DC-DROPPED `period_le_prizeFloor`. Since `not_gaussianEnergy
Bound_of_deep` machine-proves that raw bound FALSE at prize depth, the joint premise set
`hwrap ∧ hanchor ∧ (W ≤ slack)` is **jointly unsatisfiable at the prize scale** — the
capstone proves
nothing there. (This also overlaps the §6 / c.154 "good-prime pigeonhole" refutation: the prize is
∀-field-universal, so a good-prime existence route cannot reach it; here we pin the
*mechanism* — the
good-prime energy bridge is the DC-refuted raw bound.)

This file locks the audit's first vacuity finding as a kernel-checked Lane-3 constraint lemma,
independent of `_ThesisCapstone` (no import of it), on the real `rEnergy` / `GaussianEnergyBound`:

> `goodPrime_energyBridge_eq_rawEnergyBound` : the STEP-2 energy bridge `E_r ≤ Wick` produced from
> `E_r = E0 + W`, `E0 + slack ≤ Wick`, `W ≤ slack` is exactly `GaussianEnergyBound G r` (the
raw bound).

> `thesisCapstone_goodPrime_premises_vacuous_at_prize` : at prize depth (`q·(2r−1)‼·|G|^r <
|G|^{2r}`),
> NO `(E0, slack, W)` can satisfy `E_r = E0 + W ∧ E0 + slack ≤ Wick ∧ W ≤ slack` — they
would force the
> raw bound `not_gaussianEnergyBound_of_deep` refutes. The good-prime route is empty at the prize.

**Honest status.** A constraint lemma (refutation-with-mechanism), NOT progress on CORE. Makes the
audit's prose vacuity finding kernel-checked: the thesis capstone's good-prime energy bridge
is the raw
DC-included energy bound in disguise, empty at the prize scale (consistent with the §6
∀-universality
refutation of good-prime routes). The genuine open object stays the DC-subtracted moment / char-`p`
coherence (BGK/Paley wall). No CORE / cancellation / completion / anti-concentration /
moment-saving /
capacity claim. Prize CORE stays OPEN.

Issue #444 / #407.
-/

namespace ArkLib.ProximityGap.Frontier.ThesisCapstoneGoodPrimeVacuousAtPrize

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyEssential
open ArkLib.ProximityGap.GaussPeriodMomentBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The good-prime energy bridge IS the raw energy bound.** From the wraparound decomposition
`E_r = E0 + W`, the char-0 anchor `E0 + slack ≤ Wick` (`Wick = (2r−1)‼·|G|^r`), and the good-prime
selection `W ≤ slack`, STEP 2 of the thesis capstone derives `E_r ≤ Wick`, which IS
`GaussianEnergyBound G r` (the raw DC-included bound). -/
theorem goodPrime_energyBridge_eq_rawEnergyBound (G : Finset F) (r : ℕ) {E0 slack W : ℝ}
    (hwrap : (rEnergy G r : ℝ) = E0 + W)
    (hanchor : E0 + slack ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
    (hgood : W ≤ slack) :
    GaussianEnergyBound G r := by
  unfold GaussianEnergyBound
  rw [hwrap]; linarith

/-- **The thesis-capstone good-prime premises are vacuous at prize depth.** At any depth
where the DC
mass beats Wick (`q·(2r−1)‼·|G|^r < |G|^{2r}`, the `n ≥ 64`, `r ≈ log q` regime), NO `(E0,
slack, W)`
satisfies the joint premise set `E_r = E0 + W ∧ E0 + slack ≤ Wick ∧ W ≤ slack`: it would
force the raw
energy bound (`goodPrime_energyBridge_eq_rawEnergyBound`), which `not_gaussianEnergyBound_of_deep`
refutes. So the thesis capstone's good-prime route proves nothing at the prize. -/
theorem thesisCapstone_goodPrime_premises_vacuous_at_prize {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hdeep : (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
      < (G.card : ℝ) ^ (2 * r)) :
    ¬ ∃ E0 slack W : ℝ, (rEnergy G r : ℝ) = E0 + W
        ∧ E0 + slack ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ∧ W ≤ slack := by
  rintro ⟨E0, slack, W, hwrap, hanchor, hgood⟩
  exact not_gaussianEnergyBound_of_deep hψ G r hdeep
    (goodPrime_energyBridge_eq_rawEnergyBound G r hwrap hanchor hgood)

end ArkLib.ProximityGap.Frontier.ThesisCapstoneGoodPrimeVacuousAtPrize

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.ThesisCapstoneGoodPrimeVacuousAtPrize in
#print axioms goodPrime_energyBridge_eq_rawEnergyBound
open ArkLib.ProximityGap.Frontier.ThesisCapstoneGoodPrimeVacuousAtPrize in
#print axioms thesisCapstone_goodPrime_premises_vacuous_at_prize
