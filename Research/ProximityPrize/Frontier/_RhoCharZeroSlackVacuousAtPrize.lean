/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sol
-/
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyEssential

/-!
# The char-0-slack `ρ ≤ 1` premise is the RAW energy bound — vacuous at prize depth (#444 / #407)

The adversarial audit (`DISPROOF_LOG.md`, 2026-06-19) flagged a NEW vacuity: the sub-theorem
`_RhoDecomposition.wraparound_within_char0_slack_suffices` derives the prize criterion `ρ_r
≤ 1` from
the premise `hwrap : W ≤ Wick − E0`. Under the file's own wraparound encoding `W = E_r − E0` (the
wraparound surplus is the full energy minus the char-0 energy) and `Wick = (2r−1)‼·|G|^r`,
that premise
is *algebraically identical* to the **raw DC-included energy bound** `E_r ≤ Wick`
(`GaussPeriodMomentBound.GaussianEnergyBound`), which
`DCEnergyEssential.not_gaussianEnergyBound_of_deep`
machine-proves FALSE at prize depth (the DC mass `|G|^{2r}/q` exceeds `Wick` for `n ≥ 64`,
`r ≈ log q`).
So that `ρ ≤ 1` rung is **vacuously discharged exactly at the prize scale** — it proves
nothing there.

This file locks the audit's finding as a kernel-checked Lane-3 / Lever-A constraint lemma,
independent
of `_RhoDecomposition` (no import of it), stated directly on the real
`rEnergy`/`GaussianEnergyBound`
objects:

> `char0_slack_premise_iff_rawEnergy` : with `W = E_r − E0` and `Wick = (2r−1)‼·|G|^r`, the premise
> `W ≤ Wick − E0` is EQUIVALENT to `GaussianEnergyBound G r` (the raw `E_r ≤ Wick`). (Pure algebra:
> add `E0` to both sides.)

> `char0_slack_premise_vacuous_at_prize` : at prize depth (`q·(2r−1)‼·|G|^r < |G|^{2r}`, the
`n ≥ 64`,
> `r ≈ log q` regime per `probe_dc_essential.py`), the char-0-slack premise `W ≤ Wick − E0`
> (`W = E_r − E0`) CANNOT hold — it is equivalent to the raw-energy bound, refuted by
> `not_gaussianEnergyBound_of_deep`. So any `ρ ≤ 1` route through the char-0 slack alone is
> vacuous-at-prize; the genuine slack must come from the DC term (`(n^{2r} − Wick)/q`), not
the char-0
> component.

**Honest status.** This is a *constraint lemma* (a refutation-with-mechanism), NOT progress
on CORE. It
makes the audit's prose finding kernel-checked: the char-0-slack `ρ ≤ 1` shortcut is the raw
DC-included
energy bound in disguise, hence empty at the prize scale. The genuine open object remains the
DC-subtracted moment / char-`p` coherence (BGK/Paley wall). No CORE / cancellation / completion /
anti-concentration / moment-saving / capacity claim. Prize CORE stays OPEN.

Issue #444 / #407.
-/

namespace ArkLib.ProximityGap.Frontier.RhoCharZeroSlackVacuousAtPrize

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyEssential
open ArkLib.ProximityGap.GaussPeriodMomentBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The char-0-slack premise IS the raw energy bound.** With the wraparound encoding
`W = E_r − E0` and the Wick ceiling `Wick = (2r−1)‼·|G|^r`, the char-0-slack premise `W ≤ Wick − E0`
(the `hwrap` of `_RhoDecomposition.wraparound_within_char0_slack_suffices`) is equivalent to
`GaussianEnergyBound G r`, the raw DC-included energy bound `E_r ≤ Wick`. Pure algebra:
cancel `E0`. -/
theorem char0_slack_premise_iff_rawEnergy (G : Finset F) (r : ℕ) (E0 : ℝ) :
    ((rEnergy G r : ℝ) - E0
        ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r - E0)
      ↔ GaussianEnergyBound G r := by
  unfold GaussianEnergyBound
  constructor <;> intro h <;> linarith

/-- **The char-0-slack `ρ ≤ 1` route is vacuous at prize depth.** At any depth where the DC
mass beats
Wick (`q·(2r−1)‼·|G|^r < |G|^{2r}`, the `n ≥ 64`, `r ≈ log q` regime), the char-0-slack premise
`E_r − E0 ≤ Wick − E0` (`W = E_r − E0`) CANNOT hold: it is equivalent to the raw-energy bound
(`char0_slack_premise_iff_rawEnergy`), which `not_gaussianEnergyBound_of_deep` refutes. So the
char-0-slack shortcut to `ρ ≤ 1` proves nothing at the prize; the real slack must be the DC term. -/
theorem char0_slack_premise_vacuous_at_prize {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (E0 : ℝ)
    (hdeep : (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
      < (G.card : ℝ) ^ (2 * r)) :
    ¬ ((rEnergy G r : ℝ) - E0
        ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r - E0) := by
  rw [char0_slack_premise_iff_rawEnergy G r E0]
  exact not_gaussianEnergyBound_of_deep hψ G r hdeep

end ArkLib.ProximityGap.Frontier.RhoCharZeroSlackVacuousAtPrize

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.RhoCharZeroSlackVacuousAtPrize in
#print axioms char0_slack_premise_iff_rawEnergy
open ArkLib.ProximityGap.Frontier.RhoCharZeroSlackVacuousAtPrize in
#print axioms char0_slack_premise_vacuous_at_prize
